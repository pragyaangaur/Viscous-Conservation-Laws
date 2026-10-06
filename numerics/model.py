"""Small models with exact linear symmetries, shared by the experiments.

Parameters are flat vectors. Each model exposes loss, grad and a list of
symmetric generators A (as functions theta -> A theta) whose quadratic forms
<theta, A theta> are conserved by gradient flow.
"""
import numpy as np


class ReLUNet:
    """Two-layer ReLU net f(x) = sum_i a_i relu(w_i . x), squared loss.

    Rescaling a_i -> a_i / c, w_i -> c w_i leaves the loss unchanged, so the
    generator A_i is -1 on a_i, +1 on w_i and 0 elsewhere. ||A_i|| = 1.
    """

    def __init__(self, d=5, h=4, n=40, seed=0):
        rng = np.random.default_rng(seed)
        self.d, self.h = d, h
        self.X = rng.normal(size=(n, d))
        teacher = rng.normal(size=(d, 2))
        self.Y = np.maximum(self.X @ teacher, 0).sum(1)
        self.dim = h + h * d

    def split(self, th):
        return th[: self.h], th[self.h :].reshape(self.h, self.d)

    def loss(self, th):
        a, W = self.split(th)
        r = np.maximum(self.X @ W.T, 0) @ a - self.Y
        return 0.5 * np.mean(r**2)

    def grad(self, th):
        a, W = self.split(th)
        pre = self.X @ W.T
        H = np.maximum(pre, 0)
        r = H @ a - self.Y
        ga = H.T @ r / len(r)
        gW = ((r[:, None] * (pre > 0)) * a[None, :]).T @ self.X / len(r)
        return np.concatenate([ga, gW.ravel()])

    def A(self, i):
        """Diagonal of the generator for neuron i."""
        diag = np.zeros(self.dim)
        diag[i] = -1.0
        diag[self.h + i * self.d : self.h + (i + 1) * self.d] = 1.0
        return diag

    def Q(self, th, i):
        return th @ (self.A(i) * th)

    def init(self, seed=1, scale_a=1.0, scale_w=1.0):
        rng = np.random.default_rng(seed)
        a = scale_a * rng.normal(size=self.h)
        W = scale_w * rng.normal(size=(self.h, self.d)) / np.sqrt(self.d)
        return np.concatenate([a, W.ravel()])


class LinearNet:
    """Two-layer linear net Y ~ W2 W1 X. GL(r) symmetry W1 -> G W1,
    W2 -> W2 G^{-1}. The conserved matrix is C = W1 W1^T - W2^T W2."""

    def __init__(self, din=6, r=4, dout=3, n=30, seed=0):
        rng = np.random.default_rng(seed)
        self.din, self.r, self.dout = din, r, dout
        self.X = rng.normal(size=(din, n))
        self.Y = rng.normal(size=(dout, din)) @ self.X
        self.dim = r * din + dout * r

    def split(self, th):
        W1 = th[: self.r * self.din].reshape(self.r, self.din)
        W2 = th[self.r * self.din :].reshape(self.dout, self.r)
        return W1, W2

    def loss(self, th):
        W1, W2 = self.split(th)
        R = W2 @ W1 @ self.X - self.Y
        return 0.5 * np.sum(R**2) / self.X.shape[1]

    def grad(self, th):
        W1, W2 = self.split(th)
        R = (W2 @ W1 @ self.X - self.Y) / self.X.shape[1]
        g1 = W2.T @ R @ self.X.T
        g2 = R @ (W1 @ self.X).T
        return np.concatenate([g1.ravel(), g2.ravel()])

    def C(self, th):
        W1, W2 = self.split(th)
        return W1 @ W1.T - W2.T @ W2

    def init(self, seed=1, scale=0.5):
        rng = np.random.default_rng(seed)
        return scale * rng.normal(size=self.dim)
