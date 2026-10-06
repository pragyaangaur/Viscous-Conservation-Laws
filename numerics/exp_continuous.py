"""Continuous-time checks.

E1. Heavy ball m x'' + g x' = -grad L. Exact identity
    Q(inf) - Q(0) = (2m/g) int <x', A x'> dt   (start at rest)
    and bound |dQ| <= 2 m ||A|| (L0 - Linf) / g^2.
E1b. First-order coefficient: dQ / m -> (2/g^3) int <grad L, A grad L> dt
    along gradient flow g x' = -grad L, as m -> 0.
E1c. Sharpness: a scalar neuron L = (a w - y)^2 / 2 started at a = R, w = 0.
    The ratio dQ / bound tends to 1 as R grows.
E2. Nesterov ODE x'' + (r/t) x' = -grad L. Exact identity
    Q(inf) - Q(0) = (2/(r-1)) int t <x', A x'> dt
    and (r-1) int t |x'|^2 = 2 int t (L - L*) - T^2 (E_T - L*).
"""
import numpy as np
from scipy.integrate import solve_ivp

from model import LinearNet

# Smooth model for the ODE checks: a two-layer linear net. The scalar law
# Q = <theta, A theta> with A = generator of X = e1 e1^T, i.e. C[0,0].
net = LinearNet()
n = net.dim
W1m = np.zeros((net.r, net.din)); W1m[0, :] = 1.0
W2m = np.zeros((net.dout, net.r)); W2m[:, 0] = -1.0
A0 = np.concatenate([W1m.ravel(), W2m.ravel()])  # diagonal generator, ||A|| = 1
net.Q = lambda th, i: th @ (A0 * th)
th0 = net.init()


def heavy_ball(m, g, T, th_init, L, grad, A):
    # state: x, v, int <v,Av>, int |v|^2
    def rhs(t, s):
        x, v = s[:n_], s[n_ : 2 * n_]
        return np.concatenate([v, (-g * v - grad(x)) / m, [v @ (A * v), v @ v]])

    n_ = len(th_init)
    s0 = np.concatenate([th_init, np.zeros(n_), [0.0, 0.0]])
    sol = solve_ivp(rhs, [0, T], s0, method="DOP853", rtol=1e-11, atol=1e-13)
    return sol.y[:, -1], n_


def report_heavy_ball():
    print("E1  heavy ball, linear net, C[0,0], gamma = 1")
    print(f"{'m':>6} {'dQ':>12} {'(2m/g)intK':>12} {'bound':>11} {'ratio':>6} {'dQ/m':>9}")
    for m in [0.003, 0.01, 0.03, 0.1, 0.3, 1.0]:
        s, n_ = heavy_ball(m, 1.0, 600, th0, net.loss, net.grad, A0)
        x, v, intK = s[:n_], s[n_ : 2 * n_], s[2 * n_]
        dQ = net.Q(x, 0) - net.Q(th0, 0)
        ident = 2 * m * intK - m * 2 * (v @ (A0 * x))  # includes the Q'(T) term
        bound = 2 * m * (net.loss(th0) - net.loss(x))
        print(f"{m:6.3f} {dQ:12.5e} {ident:12.5e} {bound:11.4e} {abs(dQ)/bound:6.3f} {dQ/m:9.5f}")

    # first-order coefficient along gradient flow
    def rhs(t, s):
        x = s[:n]
        gr = net.grad(x)
        return np.concatenate([-gr, [gr @ (A0 * gr)]])

    sol = solve_ivp(rhs, [0, 600], np.concatenate([th0, [0.0]]), method="DOP853", rtol=1e-11, atol=1e-13)
    print(f"E1b predicted dQ/m as m->0: 2 int <gradL, A gradL> = {2*sol.y[-1,-1]:.5f}")


def report_sharpness():
    print("\nE1c sharpness on the scalar neuron L = (a w - 1)^2/2, a0 = R, w0 = 0, m = 0.05")
    L = lambda x: 0.5 * (x[0] * x[1] - 1) ** 2
    grad = lambda x: np.array([(x[0] * x[1] - 1) * x[1], (x[0] * x[1] - 1) * x[0]])
    A = np.array([-1.0, 1.0])
    for R in [1, 2, 4, 8, 16]:
        x0 = np.array([float(R), 0.0])
        s, n_ = heavy_ball(0.05, 1.0, 400, x0, L, grad, A)
        x = s[:2]
        dQ = (x[1] ** 2 - x[0] ** 2) - (x0[1] ** 2 - x0[0] ** 2)
        bound = 2 * 0.05 * (L(x0) - L(x))
        print(f"  R={R:3d}  dQ={dQ:.5e}  bound={bound:.5e}  ratio={dQ/bound:.5f}")


def report_nesterov(r=3.0, T=3000.0):
    print(f"\nE2  Nesterov ODE x'' + ({r:g}/t) x' = -grad L, linear net, C[0,0]")
    Lstar = None

    def rhs(t, s):
        x, v = s[:n], s[n : 2 * n]
        return np.concatenate([v, -(r / t) * v - net.grad(x), [t * (v @ (A0 * v)), t * (v @ v), t * net.loss(x)]])

    t0 = 1e-8
    s0 = np.concatenate([th0, np.zeros(n), [0, 0, 0]])
    sol = solve_ivp(rhs, [t0, T], s0, method="DOP853", rtol=1e-11, atol=1e-13, dense_output=True)
    for Tk in [100, 300, 1000, 3000]:
        s = sol.sol(Tk)
        x, v = s[:n], s[n : 2 * n]
        dQ = net.Q(x, 0) - net.Q(th0, 0)
        print(f"  T={Tk:5d}  dQ={dQ:.6e}  (2/(r-1)) int t K={2/(r-1)*s[2*n]:.6e}  L={net.loss(x):.3e}  |v|={np.linalg.norm(v):.1e}")
    s = sol.sol(T)
    x, v = s[:n], s[n : 2 * n]
    Lstar = net.loss(x)
    ET = 0.5 * v @ v + net.loss(x)
    lhs = (r - 1) * s[2 * n + 1]
    rhs_ = 2 * (s[2 * n + 2] - Lstar * (T**2 - t0**2) / 2) - T**2 * (ET - Lstar)
    print(f"  energy identity at T: (r-1) int t|v|^2 = {lhs:.6e}, 2 int t(L-L*) - T^2(E-L*) = {rhs_:.6e}")


if __name__ == "__main__":
    report_heavy_ball()
    report_sharpness()
    report_nesterov()
