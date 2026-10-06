"""Checks for the Nesterov dichotomy theorem.

N1. The exact NAG identity Q_N - Q_0 = sum_i w_i F_i with Nesterov weights
    w_i = 1 + i/2 - i(i+1)(i+2)/(2N(N+1)) and forcing
    F_i = beta_i (1 + beta_i) Q(theta_i - theta_{i-1}) + s^2 <g_i, A g_i>,
    on the ReLU net (indefinite A) and on a scale-invariant model (A = I).
N2. Dichotomy on the scale-invariant model L(w) = mean((X w/|w| - y)^2)/2, Q = |w|^2.
    Nesterov drift stays bounded below as s -> 0, heavy ball drift vanishes.
N3. The explicit lower bound of the theorem, 3 kappa0 tau^4 / 4096 for s <= tau^2/400, with
    tau^2 = min(rho/G, kappa0/(16 |A| |g0| H G)) as in lean/ViscosityML/NesterovLower.lean, and
    G, H estimated by sampling the ball B(theta_0, rho) with a safety margin.
"""
import numpy as np

from model import ReLUNet

rng = np.random.default_rng(3)
n, d = 30, 6
X = rng.normal(size=(n, d))
y = np.tanh(X @ rng.normal(size=d))


class ScaleInv:
    def loss(self, w):
        r = X @ w / np.linalg.norm(w) - y
        return 0.5 * np.mean(r**2)

    def grad(self, w):
        nw = np.linalg.norm(w)
        u = w / nw
        r = X @ u - y
        gu = X.T @ r / n
        return (gu - u * (u @ gu)) / nw  # Jacobian of w/|w| is (I - u u^T)/|w|


def nag(model, th0, s, N, Adiag):
    th_prev, th = th0.copy(), th0.copy()
    Ks, Gs = [], []
    for k in range(N):
        b = (k - 1) / (k + 2) if k > 0 else 0.0
        v = th - th_prev
        Ks.append(v @ (Adiag * v))
        yk = th + b * v
        g = model.grad(yk)
        Gs.append(g @ (Adiag * g))
        th_prev, th = th, yk - s * g
    return th, np.array(Ks), np.array(Gs)


def identity_check(model, th0, Adiag, s, N, label):
    th, Ks, Gs = nag(model, th0, s, N, Adiag)
    i = np.arange(N, dtype=float)
    beta = np.where(i >= 1, (i - 1) / (i + 2), 0.0)
    F = beta * (1 + beta) * Ks + s**2 * Gs
    w = 1 + i / 2 - i * (i + 1) * (i + 2) / (2 * N * (N + 1))
    dQ = th @ (Adiag * th) - th0 @ (Adiag * th0)
    print(f"  {label}: dQ = {dQ:.10e}, identity = {np.sum(w * F):.10e}, "
          f"error = {abs(dQ - np.sum(w * F)):.1e}")


def heavy_ball(model, th0, eta, beta, N):
    th, v = th0.copy(), np.zeros_like(th0)
    for _ in range(N):
        v = beta * v - eta * model.grad(th)
        th = th + v
    return th


print("N1  exact NAG identity")
r = ReLUNet()
identity_check(r, r.init(), r.A(0), 0.01, 3000, "ReLU net, neuron 0 (indefinite A)")
si = ScaleInv()
w0 = rng.normal(size=d)
identity_check(si, w0, np.ones(d), 0.05, 3000, "scale-invariant, A = I     ")

print("\nN2  dichotomy on the scale-invariant model, Q = |w|^2, |w0|^2 = %.4f" % (w0 @ w0))
print(f"  {'step':>7} {'Nesterov dQ':>12} {'HB(0.9) dQ':>12}")
for s in [1e-1, 3e-2, 1e-2, 3e-3, 1e-3]:
    N = int(4000 / np.sqrt(s))
    th, _, _ = nag(si, w0, s, N, np.ones(d))
    thh = heavy_ball(si, w0, s, 0.9, int(60 / s))
    print(f"  {s:7.0e} {th@th - w0@w0:12.5e} {thh@thh - w0@w0:12.5e}")

print("\nN3  explicit constant of the theorem")
g0 = si.grad(w0)
kappa0 = g0 @ g0
rho = 0.5 * np.linalg.norm(w0)
pts = w0 + rho * rng.uniform(-1, 1, size=(4000, d)) / np.sqrt(d)
G = max(np.linalg.norm(si.grad(p)) for p in pts)
H = 0.0
for _ in range(4000):
    a, b = pts[rng.integers(4000)], pts[rng.integers(4000)]
    if np.linalg.norm(a - b) > 1e-9:
        H = max(H, np.linalg.norm(si.grad(a) - si.grad(b)) / np.linalg.norm(a - b))
G, H = 1.2 * G, 1.5 * H  # margin over the sampled estimates
tau2 = min(rho / G, kappa0 / (16 * 1.0 * np.linalg.norm(g0) * H * G))
c = 3 * kappa0 * tau2**2 / 4096
s0 = tau2 / 400
print(f"  kappa0 = {kappa0:.4e}, G ~ {G:.3e}, H ~ {H:.3e}, tau^2 = {tau2:.4e}")
print(f"  guaranteed lower bound 3 kappa0 tau^4 / 4096 = {c:.3e} for s <= tau^2/400 = {s0:.2e}")
th, _, _ = nag(si, w0, s0, int(4000 / np.sqrt(s0)), np.ones(d))
print(f"  actual Nesterov drift at s = {s0:.2e}: {th@th - w0@w0:.4e}")
