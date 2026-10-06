"""Discrete-time checks.

D1. Heavy ball v_k = beta v_{k-1} - eta g_k, theta_{k+1} = theta_k + v_k, v_{-1} = 0.
    Exact identity Q_N - Q_0 = sum_j (1 + beta - 2 beta^(N-j)) / (1 - beta) K_j,
    K_j = <v_j, A v_j>, and the bound
    |Q_N - Q_0| <= (1+beta)/(1-beta) ||A|| sum |v_j|^2
               <= (1+beta)/(1-beta) ||A|| 2 eta (L_0 - L_N) / (2(1-beta) - eta ell).
D2. Scaling: drift ~ (1+beta) eta I / (1-beta)^2 with I = int <grad L, A grad L> dtau
    along gradient flow, so heavy ball drift vanishes as eta -> 0 at fixed beta.
D3. Nesterov, beta_k = (k-1)/(k+2), gradient at the extrapolated point. The drift
    tends to a nonzero limit as the step s -> 0 (the Nesterov ODE value).
D4. Matrix law for the linear net: nuclear norm of the change in
    C = W1 W1^T - W2^T W2 against (1+beta)/(1-beta) sum |v_j|^2.
"""
import numpy as np
from scipy.integrate import solve_ivp

from model import LinearNet, ReLUNet


def heavy_ball(model, th0, eta, beta, N, tol=None):
    th, v_prev = th0.copy(), np.zeros_like(th0)
    vs, ells = [], []
    for k in range(N):
        g = model.grad(th)
        v = beta * v_prev - eta * g
        L0, L1 = model.loss(th), model.loss(th + v)
        if v @ v > 0:
            ells.append(2 * (L1 - L0 - g @ v) / (v @ v))
        vs.append(v)
        th, v_prev = th + v, v
        if tol is not None and v @ v < tol:
            break
    return th, np.array(vs), max(ells)


def nesterov(model, th0, s, N, tol=None):
    th, th_prev = th0.copy(), th0.copy()
    vs = []
    for k in range(N):
        y = th + (k - 1) / (k + 2) * (th - th_prev) if k > 0 else th
        nxt = y - s * model.grad(y)
        vs.append(nxt - th)
        th_prev, th = th, nxt
        if tol is not None and k > 100 and vs[-1] @ vs[-1] < tol:
            break
    return th, np.array(vs)


def d1():
    net = ReLUNet()
    th0 = net.init()
    print("D1  heavy ball on the ReLU net, all four neurons")
    for eta, beta in [(0.05, 0.0), (0.05, 0.5), (0.02, 0.9), (0.005, 0.97)]:
        N = 20000
        th, vs, ell = heavy_ball(net, th0, eta, beta, N)
        N = len(vs)
        w = (1 + beta - 2 * beta ** (N - np.arange(N))) / (1 - beta)
        Lgap = net.loss(th0) - net.loss(th)
        for i in range(net.h):
            A = net.A(i)
            dQ = net.Q(th, i) - net.Q(th0, i)
            ident = np.sum(w * np.einsum("ij,j,ij->i", vs, A, vs))
            b1 = (1 + beta) / (1 - beta) * np.sum(vs * vs)
            b2 = (1 + beta) / (1 - beta) * 2 * eta * Lgap / (2 * (1 - beta) - eta * ell)
            if i == 0:
                print(f"  eta={eta} beta={beta}  ell={ell:.2f}  eta*ell/(2(1-beta))={eta*ell/(2*(1-beta)):.2f}")
            print(f"    neuron {i}: dQ={dQ: .6e}  identity err={abs(dQ-ident):.1e}  "
                  f"b1={b1:.3e}  b2={b2:.3e}  ok={abs(dQ)<=b1<=b2}")


def gf_integral(model, th0, A, T=400.0):
    n = len(th0)

    def rhs(t, s):
        g = model.grad(s[:n])
        return np.concatenate([-g, [g @ (A * g)]])

    sol = solve_ivp(rhs, [0, T], np.concatenate([th0, [0.0]]), method="DOP853", rtol=1e-11, atol=1e-13)
    return sol.y[-1, -1]


def linear_scalar_law(net):
    W1m = np.zeros((net.r, net.din)); W1m[0, :] = 1.0
    W2m = np.zeros((net.dout, net.r)); W2m[:, 0] = -1.0
    return np.concatenate([W1m.ravel(), W2m.ravel()])


def d2():
    net = LinearNet()
    th0 = net.init()
    A = linear_scalar_law(net)
    I = gf_integral(net, th0, A)
    print(f"\nD2  heavy ball scaling on the linear net, C[0,0].  I = {I:.5f}")
    print(f"  {'eta':>7} {'beta':>5} {'dQ':>12} {'(1+b) eta I/(1-b)^2':>20} {'ratio':>7}")
    for beta in [0.0, 0.5, 0.9]:
        for eta in [4e-3, 2e-3, 1e-3, 5e-4]:
            th, vs, _ = heavy_ball(net, th0, eta, beta, 10**7, tol=1e-26)
            dQ = th @ (A * th) - th0 @ (A * th0)
            pred = (1 + beta) * eta * I / (1 - beta) ** 2
            print(f"  {eta:7.0e} {beta:5.2f} {dQ:12.5e} {pred:20.5e} {dQ/pred:7.4f}")


def d3():
    net = LinearNet()
    th0 = net.init()
    A = linear_scalar_law(net)
    print("\nD3  Nesterov vs heavy ball as the step shrinks (linear net, C[0,0])")
    print("    Nesterov ODE value from exp_continuous.py: about 0.2911")
    print(f"  {'step':>7} {'Nesterov dQ':>12} {'iters':>8} {'HB(0.9) dQ':>12}")
    for s in [1e-2, 3e-3, 1e-3, 3e-4, 1e-4]:
        th, vs = nesterov(net, th0, s, 4 * 10**6, tol=1e-30)
        dQn = th @ (A * th) - th0 @ (A * th0)
        thh, _, _ = heavy_ball(net, th0, s, 0.9, 10**7, tol=1e-28)
        dQh = thh @ (A * thh) - th0 @ (A * th0)
        print(f"  {s:7.0e} {dQn:12.5e} {len(vs):8d} {dQh:12.5e}")

    rnet = ReLUNet()
    rth0 = rnet.init()
    print("  same test on the ReLU net, neuron 0")
    for s in [3e-2, 1e-2, 3e-3, 1e-3]:
        th, vs = nesterov(rnet, rth0, s, 2 * 10**6, tol=1e-30)
        thh, _, _ = heavy_ball(rnet, rth0, s, 0.9, 2 * 10**6, tol=1e-28)
        print(f"  {s:7.0e} {rnet.Q(th,0)-rnet.Q(rth0,0):12.5e} {len(vs):8d} {rnet.Q(thh,0)-rnet.Q(rth0,0):12.5e}")


def d4():
    net = LinearNet()
    th0 = net.init()
    print("\nD4  matrix law on the linear net: ||dC||_* vs (1+b)/(1-b) sum|v|^2")
    for eta, beta in [(0.01, 0.0), (0.01, 0.5), (0.003, 0.9)]:
        th, vs, _ = heavy_ball(net, th0, eta, beta, 10**6, tol=1e-28)
        dC = net.C(th) - net.C(th0)
        nuc = np.abs(np.linalg.eigvalsh(dC)).sum()
        bound = (1 + beta) / (1 - beta) * np.sum(vs * vs)
        print(f"  eta={eta} beta={beta}  ||dC||_*={nuc:.4e}  bound={bound:.4e}  ratio={nuc/bound:.3f}")


if __name__ == "__main__":
    d1()
    d2()
    d3()
    d4()
