"""Exact identities that had no direct numerical check.

C1  Theorem 9: heavy ball with Nesterov's schedule beta_k = (k-1)/(k+2),
    P_N = sum_j j(j+1)(j+2)/(N(N+1)(N+2)) K_j and
    Q_N - Q_0 = sum_j ((j+1) - j(j+1)(j+2)/(N(N+1))) K_j.
C2  Corollary 7: the matrix identity (1-b)(C_N - C_0) = sum_j (1+b-2b^(N-j)) (V1 V1^T - V2^T V2).
C3  Theorem 10: the exact weights for Nesterov's method with Nesterov's schedule.

Each check prints the largest relative error over several run lengths.
"""
import numpy as np

from model import LinearNet, ReLUNet


def hb_run(model, th0, eta, betas, N):
    th, v_prev = th0.copy(), np.zeros_like(th0)
    ths, vs = [th.copy()], []
    for k in range(N):
        v = betas(k) * v_prev - eta * model.grad(th)
        vs.append(v)
        th, v_prev = th + v, v
        ths.append(th.copy())
    return np.array(ths), np.array(vs)


def c1():
    print("C1  Theorem 9, heavy ball with Nesterov's schedule, ReLU net, neuron 0")
    net = ReLUNet()
    th0 = net.init()
    A = net.A(0)
    ths, vs = hb_run(net, th0, 0.01, lambda k: (k - 1) / (k + 2) if k > 0 else 0.0, 400)
    worst_P = worst_Q = 0.0
    for N in (1, 2, 5, 50, 200, 400):
        K = np.array([v @ (A * v) for v in vs[:N]])
        # P_N is <v_N, A theta_N>, and v_N is the step after the last one stored in vs
        v_N = (N - 1) / (N + 2) * vs[N - 1] - 0.01 * net.grad(ths[N])
        P_N = v_N @ (A * ths[N])
        j = np.arange(N)
        P_formula = np.sum(j * (j + 1) * (j + 2) / (N * (N + 1) * (N + 2)) * K)
        Q_formula = np.sum(((j + 1) - j * (j + 1) * (j + 2) / (N * (N + 1))) * K)
        dQ = ths[N] @ (A * ths[N]) - ths[0] @ (A * ths[0])
        worst_P = max(worst_P, abs(P_N - P_formula))
        worst_Q = max(worst_Q, abs(dQ - Q_formula) / max(1e-12, abs(dQ)))
    print(f"  worst error: P_N {worst_P:.1e} (absolute), Q_N - Q_0 {worst_Q:.1e} (relative)")


def c2():
    print("C2  Corollary 7, matrix identity, linear net")
    net = LinearNet()
    th0 = net.init()
    for eta, b in ((0.01, 0.0), (0.01, 0.5), (0.003, 0.9)):
        ths, vs = hb_run(net, th0, eta, lambda k: b if k > 0 else 0.0, 300)
        worst = 0.0
        for N in (1, 10, 300):
            lhs = (1 - b) * (net.C(ths[N]) - net.C(ths[0]))
            rhs = np.zeros_like(lhs)
            for j in range(N):
                V1, V2 = net.split(vs[j])
                rhs += (1 + b - 2 * b ** (N - j)) * (V1 @ V1.T - V2.T @ V2)
            worst = max(worst, np.abs(lhs - rhs).max() / max(1e-12, np.abs(lhs).max()))
        print(f"  eta={eta} beta={b}: worst relative error {worst:.1e}")


def c3():
    print("C3  Theorem 10, exact weights for Nesterov's method, ReLU net, neuron 0")
    net = ReLUNet()
    th = net.init()
    A = net.A(0)
    s, N = 0.01, 300
    ths, F, gs = [th.copy()], [], []
    th_prev = th.copy()
    for k in range(N):
        y = th + (k - 1) / (k + 2) * (th - th_prev) if k > 0 else th
        g = net.grad(y)
        nxt = y - s * g
        if k == 0:
            F.append(s * s * (g @ (A * g)))
        else:
            b = (k - 1) / (k + 2)
            d = th - th_prev
            F.append(b * (1 + b) * (d @ (A * d)) + s * s * (g @ (A * g)))
        th_prev, th = th, nxt
        ths.append(th.copy())
    worst = 0.0
    for M in (1, 2, 10, 300):
        i = np.arange(M)
        w = 1 + i / 2 - i * (i + 1) * (i + 2) / (2 * M * (M + 1))
        pred = np.sum(w * np.array(F[:M]))
        dQ = ths[M] @ (A * ths[M]) - ths[0] @ (A * ths[0])
        worst = max(worst, abs(dQ - pred) / max(1e-12, abs(dQ)))
    print(f"  worst relative error {worst:.1e}")


if __name__ == "__main__":
    c1()
    c2()
    c3()
