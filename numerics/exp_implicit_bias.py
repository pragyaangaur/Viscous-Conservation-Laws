"""Item 4: does the drift of the conserved quantity change what is learned?

Diagonal linear network w = u * v on underdetermined sparse regression. Under
gradient flow Delta_i = u_i^2 - v_i^2 is conserved and the flow is mirror descent
with phi''(w) = 1 / sqrt(Delta^2 + 4 w^2). From w0 = 0 the limit is
    w(Delta) = argmin sum_i phi_{Delta_i}(w_i)  subject to  X w = y,
whose dual solution is w_i = (|Delta_i| / 2) sinh(2 (X^T lam)_i).

We run heavy ball and Nesterov, record the final Delta, and compare the learned w
with the gradient-flow prediction from the initial Delta and from the final Delta.
"""
import numpy as np
from scipy.optimize import minimize

rng = np.random.default_rng(0)
n, d, k = 20, 60, 3
X = rng.normal(size=(n, d)) / np.sqrt(n)
w_star = np.zeros(d)
w_star[:k] = [1.0, -0.8, 0.6]
y = X @ w_star
alpha = 0.1


def loss_grad(u, v):
    r = X @ (u * v) - y
    g = X.T @ r
    return 0.5 * r @ r, g * v, g * u


def predict(Delta):
    a = np.abs(Delta)

    def dual(lam):
        z = 2 * (X.T @ lam)
        z = np.clip(z, -60, 60)
        f = np.sum(a / 4 * np.cosh(z)) - lam @ y
        gr = X @ (a / 2 * np.sinh(z)) - y
        return f, gr

    res = minimize(dual, np.zeros(n), jac=True, method="BFGS", options={"gtol": 1e-12, "maxiter": 20000})
    return np.abs(Delta) / 2 * np.sinh(np.clip(2 * (X.T @ res.x), -60, 60))


def run(method, eta, beta=0.0, N=400000):
    u, v = np.full(d, alpha), np.zeros(d)
    u_prev, v_prev = u.copy(), v.copy()
    for t in range(N):
        if method == "hb":
            _, gu, gv = loss_grad(u, v)
            un = u - eta * gu + beta * (u - u_prev)
            vn = v - eta * gv + beta * (v - v_prev)
        else:
            m = (t - 1) / (t + 2) if t > 0 else 0.0
            yu, yv = u + m * (u - u_prev), v + m * (v - v_prev)
            _, gu, gv = loss_grad(yu, yv)
            un, vn = yu - eta * gu, yv - eta * gv
        u_prev, v_prev, u, v = u, v, un, vn
    return u, v


Delta0 = np.full(d, alpha**2)
w_gf = predict(Delta0)
print(f"alpha = {alpha}, ground truth l1 = {np.abs(w_star).sum():.4f}")
print(f"GF prediction from Delta0: l1 = {np.abs(w_gf).sum():.4f}, err to w* = {np.linalg.norm(w_gf - w_star):.2e}")
print(f"{'run':>22} {'eta/(1-b)^2':>11} {'max|dDelta|':>11} {'l1(w)':>8} {'|w-w*|':>9} "
      f"{'|w-pred0|':>10} {'|w-predEnd|':>11}")
for label, method, eta, beta in [
    ("GD", "hb", 0.05, 0.0),
    ("HB beta=0.5", "hb", 0.05, 0.5),
    ("HB beta=0.9", "hb", 0.02, 0.9),
    ("HB beta=0.9", "hb", 0.05, 0.9),
    ("HB beta=0.95", "hb", 0.03, 0.95),
    ("Nesterov s=0.05", "nag", 0.05, 0.0),
    ("Nesterov s=0.01", "nag", 0.01, 0.0),
]:
    u, v = run(method, eta, beta)
    w = u * v
    D = u**2 - v**2
    pe = predict(D)
    lam = eta / (1 - beta) ** 2 if method == "hb" else float("nan")
    print(f"{label:>22} {lam:11.3f} {np.max(np.abs(D - Delta0)):11.3e} {np.abs(w).sum():8.4f} "
          f"{np.linalg.norm(w - w_star):9.2e} {np.linalg.norm(w - w_gf):10.2e} {np.linalg.norm(w - pe):11.2e}")
