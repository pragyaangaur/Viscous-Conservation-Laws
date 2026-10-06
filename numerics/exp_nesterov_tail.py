"""Why the Nesterov drift grows on the ReLU net: track the loss gap and the running
drift against continuous time t = k sqrt(s) along discrete Nesterov."""
import numpy as np
from model import ReLUNet, LinearNet
from exp_discrete import linear_scalar_law

def run(model, th0, A, s, N, label):
    th, th_prev = th0.copy(), th0.copy()
    Q0 = th0 @ (A * th0)
    marks = {int(10 ** e) for e in np.arange(2, np.log10(N) + 0.01, 0.5)}
    print(f"{label}, step {s:g}")
    print(f"  {'t':>9} {'L':>10} {'t^2 L':>9} {'dQ':>9}")
    for k in range(N + 1):
        if k in marks:
            t = k * np.sqrt(s)
            L = model.loss(th)
            print(f"  {t:9.1f} {L:10.3e} {t*t*L:9.3f} {th@(A*th)-Q0:9.4f}")
        y = th + (k - 1) / (k + 2) * (th - th_prev) if k > 0 else th
        th_prev, th = th, y - s * model.grad(y)

r = ReLUNet(); run(r, r.init(), r.A(0), 1e-2, 3 * 10**6, "ReLU net, neuron 0")
l = LinearNet(); run(l, l.init(), linear_scalar_law(l), 1e-2, 10**6, "linear net, C[0,0]")
