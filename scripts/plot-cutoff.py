#!/usr/bin/env python3
"""Plot the cutoff phenomenon from the exact formulas proved in Lean.

Writes docs/cutoff-profiles.png and docs/critical-time.png. The curves use the closed forms of
`Cutfast/Distances.lean` (`wassersteinSq_solution`, `relEntropy_solution`, `fisherInfo_solution`),
with `a = (1 - e^{-t/α})^α`, `|h|² = e^{-2t} r² d` (the supremum over `|x₀| ≤ r√d` is attained
at `|x₀| = r√d`), `κ = d(1-m)`, and the second moment `M₂ = ∫|x|² v_∞` from eq. (Bac) of
Lemma 3.1, evaluated exactly with log-Gamma functions.
"""
import pathlib

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
from scipy.special import gammaln

ROOT = pathlib.Path(__file__).resolve().parent.parent
DOCS = ROOT / "docs"

SURFACE = "#fcfcfb"
INK = "#0b0b0b"
INK_2 = "#52514e"
GRID = "#e4e3df"
# Ordinal blue ramp (steps 250, 400, 500, 600, 700), validated light→dark.
RAMP = ["#86b6ef", "#3987e5", "#256abf", "#184f95", "#0d366b"]
ACCENT = "#2a78d6"

ALPHA = 1.0  # m = (d-1)/d, the Sobolev exponent
R = 1.0
DIMS = [10, 100, 1_000, 10_000, 1_000_000]


def second_moment(d: int, alpha: float) -> float:
    """M₂ of v_∞ for α > 1/2: eq. (Bac) with a = 2, p = dα/(2α-1), b = (2α-1)/(2(α(d-2)+1))."""
    p = d * alpha / (2 * alpha - 1)
    b = (2 * alpha - 1) / (2 * (alpha * (d - 2) + 1))
    log_k = (d / 2) * np.log(np.pi) + gammaln(p - d / 2) - p * np.log(b) - gammaln(p)
    log_ratio = (gammaln((d + 2) / 2) + gammaln(p - (d + 2) / 2)
                 - gammaln(d / 2) - gammaln(p - d / 2))
    return float(np.exp(2 / (2 * p - d) * log_k + log_ratio))


def distances(d: int, alpha: float, t: np.ndarray) -> dict[str, np.ndarray]:
    m = ((d - 2) * alpha + 1) / (d * alpha)
    kappa = d * (1 - m)
    m2 = second_moment(d, alpha)
    a = (1 - np.exp(-t / alpha)) ** alpha
    h2 = np.exp(-2 * t) * R ** 2 * d
    return {
        "W₂²": (1 - a) ** 2 * m2 + h2,
        "Hₘ": m2 * ((1 - a ** kappa) / kappa - (1 - a ** 2) / 2) + h2 / 2,
        "Iₘ": a ** 2 * (1 - a ** (-1 / alpha)) ** 2 * m2 + h2,
    }


def style(ax) -> None:
    ax.set_facecolor(SURFACE)
    ax.grid(True, which="major", color=GRID, linewidth=0.8)
    ax.set_axisbelow(True)
    for side in ("top", "right"):
        ax.spines[side].set_visible(False)
    for side in ("left", "bottom"):
        ax.spines[side].set_color(INK_2)
    ax.tick_params(colors=INK_2, labelsize=9)


def plot_profiles() -> None:
    c = np.linspace(0.05, 1.0, 800)
    fig, axes = plt.subplots(1, 3, figsize=(13, 4.4), sharey=True, facecolor=SURFACE)
    for ax, name in zip(axes, ["W₂²", "Hₘ", "Iₘ"]):
        style(ax)
        for d, color in zip(DIMS, RAMP):
            y = distances(d, ALPHA, c * np.log(d))[name]
            ax.plot(c, y, color=color, linewidth=2, label=f"d = {d:,}".replace(",", " "))
        ax.axvline(0.5, color=INK_2, linewidth=1, linestyle=(0, (4, 3)))
        ax.set_yscale("log")
        ax.set_ylim(1e-4, 1e6)
        ax.set_xlim(0.05, 1.0)
        ax.set_title(f"sup over |x₀| ≤ √d of {name}(v(t), v∞)", color=INK, fontsize=11, loc="left")
        ax.set_xlabel("t / log d", color=INK_2, fontsize=10)
        ax.text(0.51, 2e5, "critical time\n½ log d", color=INK_2, fontsize=9, va="top")
    axes[0].set_ylabel("distance (log scale)", color=INK_2, fontsize=10)
    handles, labels = axes[0].get_legend_handles_labels()
    fig.legend(handles, labels, loc="lower center", ncol=len(DIMS), frameon=False,
               fontsize=9, labelcolor=INK_2, bbox_to_anchor=(0.5, -0.02))
    fig.suptitle("Cutoff for the fast diffusion equation with m = (d−1)/d (α = 1): "
                 "the transition sharpens as d grows",
                 color=INK, fontsize=13, x=0.01, ha="left")
    fig.tight_layout(rect=(0, 0.06, 1, 0.97))
    fig.savefig(DOCS / "cutoff-profiles.png", dpi=150, facecolor=SURFACE)
    plt.close(fig)


def plot_critical_time() -> None:
    alpha = np.linspace(0.02, 3, 600)
    crit = np.maximum(1, alpha) / 2
    fig, ax = plt.subplots(figsize=(7.5, 4.4), facecolor=SURFACE)
    style(ax)
    ax.fill_between(alpha, 0, crit, color="#cde2fb", linewidth=0)
    ax.plot(alpha, crit, color=ACCENT, linewidth=2)
    ax.axvline(0.5, color=INK_2, linewidth=1, linestyle=(0, (4, 3)))
    ax.text(2.1, 0.32, "distance → +∞", color=INK, fontsize=10, ha="center")
    ax.text(0.95, 1.3, "distance → 0", color=INK, fontsize=10, ha="center")
    ax.text(0.25, 0.04, "porous medium\nm > 1", color=INK_2, fontsize=9, ha="center")
    ax.text(1.75, 0.04, "fast diffusion m < 1", color=INK_2, fontsize=9, ha="center")
    ax.text(0.53, 1.45, "α = ½: heat equation", color=INK_2, fontsize=9)
    ax.annotate("max(1, α)/2", xy=(2.2, 1.1), xytext=(2.35, 0.75), color=ACCENT, fontsize=10,
                arrowprops=dict(arrowstyle="-", color=ACCENT, linewidth=1))
    ax.set_xlim(0, 3)
    ax.set_ylim(0, 1.6)
    ax.set_xlabel("α (with m = ((d−2)α + 1)/(dα))", color=INK_2, fontsize=10)
    ax.set_ylabel("critical time / log d", color=INK_2, fontsize=10)
    ax.set_title("Theorem 1.1: critical time of the cutoff, for initial points |x₀| ≤ r√d",
                 color=INK, fontsize=12, loc="left")
    fig.tight_layout()
    fig.savefig(DOCS / "critical-time.png", dpi=150, facecolor=SURFACE)
    plt.close(fig)


def main() -> None:
    DOCS.mkdir(exist_ok=True)
    for d in DIMS:
        print(f"d = {d}: M₂/d = {second_moment(d, ALPHA) / d:.4f}  (limit 2πe = {2 * np.pi * np.e:.4f})")
    plot_profiles()
    plot_critical_time()
    print("wrote docs/cutoff-profiles.png and docs/critical-time.png")


if __name__ == "__main__":
    main()
