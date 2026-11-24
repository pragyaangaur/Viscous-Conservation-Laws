"""Early phase against tail for an indefinite generator.

For the scalar ReLU neuron L(a, w) = (a w - 1)^2 / 2 with A = diag(-1, 1), Nesterov's
method gives Q_N - Q_0 = sum_i w_i F_i with the exact weights of Theorem 10. The proof of the
dichotomy for A >= 0 keeps only the early terms, because all terms are nonnegative. Here
A is indefinite, and the script splits the sum at i = J with J + 2 = floor(tau / sqrt(s)).
It prints the early part, the tail and the total for several steps. The tail is the part
that has no proof.
"""
import numpy as np

A = np.array([-1.0, 1.0])


def grad(x):
    r = x[0] * x[1] - 1
    return np.array([x[1] * r, x[0] * r])


def run(a0, w0, s, N):
    th, prev = np.array([a0, w0], float), np.array([a0, w0], float)
    F = []
    for k in range(N):
        y = th + (k - 1) / (k + 2) * (th - prev) if k > 0 else th
        g = grad(y)
        if k == 0:
            F.append(s * s * (g @ (A * g)))
        else:
            b = (k - 1) / (k + 2)
            d = th - prev
            F.append(b * (1 + b) * (d @ (A * d)) + s * s * (g @ (A * g)))
        prev, th = th, y - s * g
    i = np.arange(N)
    w = 1 + i / 2 - i * (i + 1) * (i + 2) / (2 * N * (N + 1))
    return w * np.array(F), th @ (A * th) - (a0 * a0 * -1 + w0 * w0)


for a0, w0 in [(1.5, 0.3), (0.3, 1.5), (3.0, -0.5)]:
    print(f"start (a, w) = ({a0}, {w0})")
    print("      s      early(tau=1)        tail        total   tail/total")
    for s in [1e-2, 1e-3, 1e-4]:
        N = int(400 / np.sqrt(s))
        terms, total = run(a0, w0, s, N)
        J = int(1.0 / np.sqrt(s))
        early, tail = terms[:J].sum(), terms[J:].sum()
        print(f"{s:7.0e} {early:14.5f} {tail:14.5f} {total:12.5f} {tail / total:10.3f}")
