"""Figure 1: drift of the conserved quantity against step size, heavy ball vs Nesterov.
Numbers are the D3 rows of results_discrete.txt."""
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

s = [1e-2, 3e-3, 1e-3, 3e-4, 1e-4]
nag = [1.37326e-01, 1.71448e-01, 2.01900e-01, 2.30530e-01, 2.50522e-01]
hb = [2.07402e-01, 1.08706e-01, 3.71206e-02, 9.84170e-03, 3.09135e-03]
sr = [3e-2, 1e-2, 3e-3, 1e-3]
nag_r = [2.48289, 2.79249, 3.07378, 3.33380]
hb_r = [1.17834, 3.22355e-01, 8.26419e-02, 2.67002e-02]

fig, ax = plt.subplots(1, 2, figsize=(8.4, 3.4))
for a, (xs, n_, h_, title, ode) in zip(ax, [(s, nag, hb, "two-layer linear net", 0.2911),
                                          (sr, nag_r, hb_r, "two-layer ReLU net", None)]):
    a.loglog(xs, n_, "o-", color="#c2410c", label="Nesterov")
    a.loglog(xs, h_, "s-", color="#1d4ed8", label=r"heavy ball, $\beta=0.9$")
    if ode:
        a.axhline(ode, ls="--", color="#c2410c", lw=0.8, label="Nesterov ODE limit")
    a.set_xlabel("step size")
    a.set_title(title, fontsize=10)
    a.invert_xaxis()
    a.grid(alpha=0.3, which="both", lw=0.4)
ax[0].set_ylabel(r"$|Q(\theta_\infty)-Q(\theta_0)|$")
ax[0].legend(fontsize=8, frameon=False)
fig.tight_layout()
fig.savefig("../paper/fig_dichotomy.pdf")
fig.savefig("../paper/fig_dichotomy.png", dpi=160)
