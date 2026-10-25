# Formalization guide

This guide follows the paper `cutfast-lean.tex` statement by statement. This file is version 1
on arXiv ([arXiv:2503.11770v1](https://arxiv.org/abs/2503.11770v1)) with the corrections listed in
`ERRATA.md`, and is essentially identical to version 2
([arXiv:2503.11770v2](https://arxiv.org/abs/2503.11770v2)).
For each one it says where the Lean statement is, how the paper's objects were translated, and how
the Lean proof goes. It is meant for a mathematician who wants to check the formalization without
reading the proofs line by line.

## How to read the formalization

- **`Challenge.lean` is the only file to trust.** It contains the definitions and the 49 advertised
  statements, each with a docstring citing the paper. Everything else is proof.
- **Each statement `T` is proved by a lemma `T'`** in a module of `Cutfast/`. `Solution.lean` only
  restates `T` and applies `T'`; `lake comparator` checks that the statements of `Challenge.lean`
  and `Solution.lean` are identical and that only the axioms `propext`, `Classical.choice` and
  `Quot.sound` are used.
- **Links** below point to the statement in `Challenge.lean` and to the proving lemma.
- **API documentation** of every Cutfast declaration, with search, is at
  https://djalilchafai.github.io/cutoff-fastdiff/Cutfast.html; links to Mathlib go to its official
  documentation. It is rebuilt on demand by the `docs` job of CI, in about 7 minutes thanks to a
  cache of the documentation data of each module (about 85 minutes without it, when the cache has
  not been used for 7 days or the Mathlib or doc-gen4 version changes).

### Notation and conventions

| Paper | Lean (`Challenge.lean`) | Remarks |
|---|---|---|
| `ℝᵈ` | `E d = EuclideanSpace ℝ (Fin d)` | Euclidean norm `‖x‖` |
| `α = 1/(2 - d(1-m))` | `alpha d m` | |
| `B`, `c = c_{d,m}` (eq. (B)) | `barenblatt d m`, `barenblattConst d m` | `c` is chosen by `Classical.choose` among the constants making `B` a probability density, with junk value `0` if there is none; `barenblattConst_spec` proves that it exists and is unique |
| `v(t,x)` (eq. (FDEFPv)) | `solution d m x₀ t x` | the explicit formula, as in the paper |
| `v_∞` (eq. (vinf)) | `equilibrium d m` | |
| `u(t,x)` (eq. (sol)) | `fdeSolution d m x₀ t x` | |
| `m = ((d-2)α+1)/(dα)` | `exponentOfAlpha α d` | |
| the law `f(x) dx` | `densityMeasure f` | `volume.withDensity (ofReal ∘ f)` |
| `W₂²(μ,ν)` | `wassersteinSq μ ν : ℝ≥0∞` | infimum over all couplings, with values in `[0,∞]`; `+∞` when no coupling has finite cost |
| `Hₘ(f ∣ v_∞)` (eq. (tsalis)) | `relEntropy m f (equilibrium d m) : ℝ` | Bochner integral of `relEntropyDensity`; it is `0` if the integrand is not integrable, so integrability is always proved alongside |
| `Iₘ(f ∣ v_∞)` (eq. (fisher)) | `fisherInfo m f : ℝ≥0∞` | lower Lebesgue integral, values in `[0,∞]`; Mathlib's `gradient` is `0` where `f^{m-1}` is not differentiable, which only happens where `f = 0` or on a null set |
| `(·)₊^p` | `(max · 0) ^ p` | real power `Real.rpow`; note `0 ^ 0 = 1` |
| profiles of Lemmas 3.1, 4.1 | `fullBarenblatt d p b`, `compactBarenblatt d p b` | with the normalizing constants of eqs. (Bxc), (CBxc) |

### Map of the proof

```
Radial ─► Moments ─► Asymptotics ───────────────┐
   │         │                                  ▼
   │         └─► Barenblatt ─► Distances ─► Cutoff, CutoffRadius   (Theorems 1.1, 1.2, §1.4.3)
   │                │    ▲          │
   │                │    └─ Wasserstein (Lemma 2.1) ─► Elliptic (Lemma 2.2)
   │                ├─► PDE, FDE, HeavyTail, Entropy, DiffusionLimit (§1.2–1.4.2)
   └─► Student (Remark 3.2)                Sphere (Remark 4.3)
```

API documentation of each module: [Radial](https://djalilchafai.github.io/cutoff-fastdiff/Cutfast/Radial.html), [Moments](https://djalilchafai.github.io/cutoff-fastdiff/Cutfast/Moments.html), [Asymptotics](https://djalilchafai.github.io/cutoff-fastdiff/Cutfast/Asymptotics.html), [Barenblatt](https://djalilchafai.github.io/cutoff-fastdiff/Cutfast/Barenblatt.html), [Distances](https://djalilchafai.github.io/cutoff-fastdiff/Cutfast/Distances.html), [Cutoff](https://djalilchafai.github.io/cutoff-fastdiff/Cutfast/Cutoff.html), [CutoffRadius](https://djalilchafai.github.io/cutoff-fastdiff/Cutfast/CutoffRadius.html), [Wasserstein](https://djalilchafai.github.io/cutoff-fastdiff/Cutfast/Wasserstein.html), [Elliptic](https://djalilchafai.github.io/cutoff-fastdiff/Cutfast/Elliptic.html), [PDE](https://djalilchafai.github.io/cutoff-fastdiff/Cutfast/PDE.html), [FDE](https://djalilchafai.github.io/cutoff-fastdiff/Cutfast/FDE.html), [HeavyTail](https://djalilchafai.github.io/cutoff-fastdiff/Cutfast/HeavyTail.html), [Entropy](https://djalilchafai.github.io/cutoff-fastdiff/Cutfast/Entropy.html), [DiffusionLimit](https://djalilchafai.github.io/cutoff-fastdiff/Cutfast/DiffusionLimit.html), [Student](https://djalilchafai.github.io/cutoff-fastdiff/Cutfast/Student.html), [Sphere](https://djalilchafai.github.io/cutoff-fastdiff/Cutfast/Sphere.html) and [Defs](https://djalilchafai.github.io/cutoff-fastdiff/Cutfast/Defs.html) (the definitions of `Challenge.lean`, used by all the others).

The graph of which statement each proof uses, read from the compiled proofs, is in
[`docs/dependencies.md`](docs/dependencies.md).

The key fact behind everything is that `v(t)` is the image of `v_∞` under the affine map
`y ↦ a(t) y + e^{-t} x₀` with `a(t) = (1 - e^{-t/α})^α`
([`Barenblatt.lean` L514](Cutfast/Barenblatt.lean#L514)). Together with Lemma 2.1 and the moments
of the Barenblatt profiles, this gives exact closed forms
([`Distances.lean`](Cutfast/Distances.lean)), with `M₂ = ∫|x|² v_∞`, `h = e^{-t}x₀`,
`κ = d(1-m)`:

- `W₂²(v(t), v_∞) = (1-a)² M₂ + |h|²`;
- `Hₘ(v(t) ∣ v_∞) = M₂ ((1-a^κ)/κ - (1-a²)/2) + |h|²/2`;
- `Iₘ(v(t) ∣ v_∞) = a² (1-a^{-1/α})² M₂ + |h|²`.

These use the exact virial identity `∫|x|² v_∞ = d ∫ v_∞ᵐ`
([`Barenblatt.lean` L626](Cutfast/Barenblatt.lean#L626)), which makes the paper's `O(1)`
differences vanish.

### Size

<!-- lines:begin -->
| | Lines |
|---|---:|
| `Cutfast/*.lean` | 8,119 |
| `Challenge.lean` | 708 |
| `Solution.lean` | 589 |
| **This formalization** | **9,416** |
| Mathlib, whole library (8,536 files, all imported) | 2,330,053 |
| **Mathlib, used by the proofs** (40,060 declarations in 1,970 files) | **180,440** |

"Used" counts the source lines of the Mathlib declarations reached from the 49 theorems through statements and proofs, instances included. Not counted: 19,659 auto-generated Mathlib declarations, and 24,537 lines of Lean's core library. Generated by `scripts/count-lines.py`.
<!-- lines:end -->

---

## Section 1.2: the Barenblatt profile and the solution

### Normalization of `B` (eq. (B))
- **Lean:** [`barenblattConst_spec`](Challenge.lean#L114), proved by
  [`barenblattConst_spec'`](Cutfast/Barenblatt.lean#L294).
- **Statement:** for `d ≥ 1`, `0 < m ≠ 1`, `m > (d-2)/d`, the constant is positive, makes `B` an
  integrable probability density, and is the only such positive constant.
- **Proof:** `B_c` is rewritten as the full-space profile `(c + κ|x|²)^{-1/(1-m)}` when `m < 1`, or
  the compact profile `(c - κ|x|²)₊^{1/(m-1)}` when `m > 1`. The radial integrals of
  [`Radial.lean`](Cutfast/Radial.lean) (polar coordinates and Euler Beta integrals) give the mass
  as an explicit power of `c`, which yields existence and uniqueness
  ([`exists_unique_const`](Cutfast/Barenblatt.lean#L244)).

### `v(t)` and `v_∞` are probability densities
- **Lean:** [`solution_isProbabilityDensity`](Challenge.lean#L123) →
  [`Barenblatt.lean` L499](Cutfast/Barenblatt.lean#L499);
  [`equilibrium_isProbabilityDensity`](Challenge.lean#L129) →
  [`Barenblatt.lean` L428](Cutfast/Barenblatt.lean#L428).
- **Proof:** change of variables `x = a y + h` in `ℝᵈ`
  ([`lintegral_comp_smul_add`](Cutfast/Barenblatt.lean#L63)) reduces both to the normalization of
  `B`.

### `v` solves `∂ₜv = Δ(vᵐ) + div(xv)` (eq. (FDEFP))
- **Lean:** [`solution_hasDerivAt`](Challenge.lean#L137) →
  [`solution_hasDerivAt'`](Cutfast/PDE.lean#L126).
- **Statement:** a classical (pointwise) identity `∂ₜv = Δ(vᵐ) + d v + ⟨x, ∇v⟩` at every point
  `(t,x)`, `t > 0`, where `v > 0`. That is everywhere when `m < 1`, and inside the support when
  `m > 1`. The paper's weak formulation and uniqueness are not formalized.
- **Proof:** near a positivity point the base of the profile is positive, so `v` is smooth. The
  Laplacian of `vᵐ` comes from the radial formula
  `Δ[G(|y-h|²)] = 4|y-h|² G''(|y-h|²) + 2d G'(|y-h|²)`
  ([`laplacian_comp_normSq_sub`](Cutfast/PDE.lean#L53)), and the identity reduces to an algebraic
  one.

### The solution `u` of `∂ₜu = Δ(uᵐ)` (eq. (sol)) and the time change (eqs. (uv), (FDEFPv))
- **Lean:** [`fdeSolution_hasDerivAt`](Challenge.lean#L153) →
  [`FDE.lean` L85](Cutfast/FDE.lean#L85);
  [`fdeSolution_isProbabilityDensity`](Challenge.lean#L162) →
  [`FDE.lean` L175](Cutfast/FDE.lean#L175);
  [`solution_eq_fdeSolution`](Challenge.lean#L169) → [`FDE.lean` L194](Cutfast/FDE.lean#L194).
- **Statement:** as for `v`: pointwise PDE where `u > 0`, probability density for `t > 0`, and
  `v(t,x) = e^{dt} u(α(e^{t/α}-1), eᵗx)`.
- **Proof:** same method as for `v`; `u(t)` is the rescaling `t^{-αd} B(t^{-α}(x - x₀))`, and the
  time change is an algebraic identity on the explicit formulas.

### Initial condition `u(t), v(t) → δ_{x₀}` as `t → 0⁺`
- **Lean:** [`tendsto_fdeSolution_zero`](Challenge.lean#L176) →
  [`FDE.lean` L220](Cutfast/FDE.lean#L220);
  [`tendsto_solution_zero`](Challenge.lean#L182) → [`FDE.lean` L243](Cutfast/FDE.lean#L243).
- **Statement:** weak convergence, `∫ φ u(t) → φ(x₀)` for every bounded continuous `φ`.
- **Proof:** both are images of the fixed density `B` under `y ↦ a y + h` with `a → 0`, `h → x₀`;
  dominated convergence ([`tendsto_integral_affine`](Cutfast/FDE.lean#L62)).

### Long-time behavior (eq. (vinf))
- **Lean:** [`tendsto_solution_atTop`](Challenge.lean#L189) →
  [`FDE.lean` L263](Cutfast/FDE.lean#L263).
- **Statement:** `v(t,x) → v_∞(x)` pointwise, and `v_∞ = (C + (1-m)/(2m)|x|²)₊^{1/(m-1)}` for
  some `C > 0`.
- **Proof:** `v(t,x) = a(t)^{-d} v_∞((x - e^{-t}x₀)/a(t))` with `a(t) → 1`, and `v_∞` is
  continuous. The formula for `v_∞` uses `α(d(1-m) - 2) + 1 = 0`.

### Finite second moment iff `m > d/(d+2)`
- **Lean:** [`integrable_sq_mul_equilibrium_iff`](Challenge.lean#L196) →
  [`HeavyTail.lean` L121](Cutfast/HeavyTail.lean#L121).
- **Proof:** radial integral: `∫ u^s (C + bu)^{-p} du` is finite iff `s - p < -1`, with an explicit
  lower bound in the divergent case ([`integral_ge`](Cutfast/HeavyTail.lean#L99)).

## Section 1.3: distances and divergences

### `W₂² = +∞` for heavy tails
- **Lean:** [`wassersteinSq_eq_top`](Challenge.lean#L203) →
  [`wassersteinSq_eq_top'`](Cutfast/HeavyTail.lean#L272).
- **Statement:** if `(d-2)/d < m ≤ d/(d+2)`, then `W₂²(v(t), v_∞) = +∞` for every `t > 0`. The
  paper only notes this for `d ≤ 2`; here it is proved for all such `m`.
- **Proof:** a moment argument rather than tail asymptotics
  ([`lintegral_cost_eq_top`](Cutfast/HeavyTail.lean#L153)). With `q = 2p - d ∈ (0,2]`, the moments
  `N(r) = ∫|x|^r v_∞` are finite for `r < q` and blow up as `r → q⁻`. A coupling of
  `law(aX + h)` and `law(X)`, `0 < a < 1`, with finite quadratic cost would give
  `N(r) ≤ (c²a)^r N(r) + K` uniformly in `r`, a contradiction.

### Entropy dissipation `dHₘ/dt = -Iₘ`
- **Lean:** [`relEntropy_hasDerivAt`](Challenge.lean#L212) →
  [`Entropy.lean` L18](Cutfast/Entropy.lean#L18).
- **Statement:** for `m > d/(d+2)` and `t > 0`, `Iₘ(v(t)) < ∞` and
  `d/dt Hₘ(v(t) ∣ v_∞) = -Iₘ(v(t) ∣ v_∞)`.
- **Proof:** differentiate the exact closed form of `Hₘ(v(t))` in `t` and compare with the closed
  form of `Iₘ(v(t))` (see the map of the proof above). This is specific to the explicit solution,
  not a general dissipation theorem.

### Bregman form (eq. (tsalisbis))
- **Lean:** [`relEntropy_eq_bregman`](Challenge.lean#L222) →
  [`Entropy.lean` L122](Cutfast/Entropy.lean#L122).
- **Statement:** for a probability density `f` with finite second moment and `fᵐ` integrable, and
  vanishing outside `supp v_∞` when `m > 1`: the integrand is integrable, `Hₘ` equals the Bregman
  form, and `Hₘ ≥ 0`.
- **Proof:** on `supp v_∞`, `v_∞^{m-1} = C + (1-m)/(2m)|x|²`, so the two integrands differ by
  `mC(f - v_∞)/(m-1)`, whose integral vanishes. Nonnegativity is pointwise convexity (Bernoulli's
  inequality, [`bregman_nonneg`](Cutfast/Entropy.lean#L72)).

### The Tsallis function
- **Lean:** [`tsallis_strictConvexOn_tendsto_log`](Challenge.lean#L237) →
  [`Entropy.lean` L219](Cutfast/Entropy.lean#L219).
- **Statement:** `x ↦ (xᵐ-1)/(m-1)` is strictly convex on `[0,∞)`, and `(xᵐ - x)/(m-1) → x log x`
  as `m → 1`. The paper's original claim (without subtracting `(x-1)/(m-1)`) is false; it is
  disproved in [`tsallis_not_tendsto`](Cutfast/Entropy.lean#L195) (`ERRATA.md`, item 13).

## Section 1.4.2: diffusion limit `m → 1`

- **Lean:** [`tendsto_barenblatt_one`](Challenge.lean#L245) →
  [`DiffusionLimit.lean` L487](Cutfast/DiffusionLimit.lean#L487);
  [`tendsto_fdeSolution_one`](Challenge.lean#L252) (heat kernel) →
  [L494](Cutfast/DiffusionLimit.lean#L494);
  [`tendsto_solution_one`](Challenge.lean#L260) (Mehler kernel) →
  [L502](Cutfast/DiffusionLimit.lean#L502).
- **Statement:** pointwise limits at fixed `d`, `t`, `x`, as `m → 1` from both sides.
- **Proof:** `B` is the full-space (`m < 1`) or compact (`m > 1`) profile of shape
  `p = 1/|1-m| → ∞` and scale `κ` with `pκ → 1/4`. The Gamma ratio asymptotics
  `log Γ(y + a) - log Γ(y) - a log y → 0`, obtained from the log-convexity of `Γ`
  ([`tendsto_gammaDefect_half`](Cutfast/DiffusionLimit.lean#L88)), show that the normalizing
  constant tends to `(4π)^{-d/2}`.

## Theorems 1.1 and 1.2: the cutoff phenomenon

| Paper | Distance | Lean statement | Proof |
|---|---|---|---|
| Theorem 1.1 | `W₂²` | [`cutoff_wassersteinSq`](Challenge.lean#L271) | [`Cutoff.lean` L819](Cutfast/Cutoff.lean#L819) |
| Theorem 1.1 | `Hₘ` | [`cutoff_relEntropy`](Challenge.lean#L287) | [`Cutoff.lean` L841](Cutfast/Cutoff.lean#L841) |
| Theorem 1.1 | `Iₘ` | [`cutoff_fisherInfo`](Challenge.lean#L305) | [`Cutoff.lean` L867](Cutfast/Cutoff.lean#L867) |
| Theorem 1.2 | `W₂²` | [`cutoff_fixedExponent_wassersteinSq`](Challenge.lean#L320) | [`Cutoff.lean` L886](Cutfast/Cutoff.lean#L886) |
| Theorem 1.2 | `Hₘ` | [`cutoff_fixedExponent_relEntropy`](Challenge.lean#L332) | [`Cutoff.lean` L900](Cutfast/Cutoff.lean#L900) |
| Theorem 1.2 | `Iₘ` | [`cutoff_fixedExponent_fisherInfo`](Challenge.lean#L345) | [`Cutoff.lean` L918](Cutfast/Cutoff.lean#L918) |

- **Statement:** each theorem is a conjunction of the two limits of the paper:
  `sup_{|x₀| ≤ r√d} dist(v(t_d), v_∞) → +∞` for `t_d = (1-ε)·T·log d`, and `→ 0` for
  `t_d = (1+ε)·T·log d`, with `T = max(1,α)/2` (Theorem 1.1, `m = exponentOfAlpha α d`) or
  `T = 1/2` (Theorem 1.2, fixed `m > 1`). Choices to check:
  - the `+∞` limit assumes `ε < 1`, so that `t_d > 0` (`ERRATA.md`, item 3); the `0` limit holds
    for every `ε > 0`;
  - the supremum is taken in `[0,∞]` for `W₂²` and `Iₘ`, and in `EReal` for `Hₘ`;
  - the `Hₘ` theorems also prove that the entropy integrand is integrable for every `t > 0` and
    `|x₀| ≤ r√d`, once `d` is large, so that `Hₘ` is not a junk value.
- **Proof:** from the exact closed forms, with `u = e^{-t/α}` and `a = (1-u)^α`: for `u ≤ 1/2`,
  each distance is at most `C u² M₂ + C' e^{-2t}|x₀|²`, at least `c e^{-2t}|x₀|²`, and, when
  `α ≥ 1`, at least `c u² M₂`. Since `M₂ ≍ d` (Lemmas 3.1, 4.1, 4.2), the result follows from
  `d u² = d^{1 - 2t/(α log d)}` and `d e^{-2t} = d^{1 - 2t/log d}`. The distances depend on `x₀`
  only through `|x₀|`, increasingly, so the supremum is attained on the sphere `|x₀| = r√d`.
  Only the bounds `cd ≤ M₂ ≤ Cd` are used, not the `(2πe)` constants.

## Section 1.4.3: other sizes of the set of initial points

| Paper | Distance | Lean statement | Proof |
|---|---|---|---|
| Theorem 1.1, radius `r d^θ` | `W₂²` | [`cutoff_wassersteinSq_radius`](Challenge.lean#L356) | [`CutoffRadius.lean` L393](Cutfast/CutoffRadius.lean#L393) |
| | `Hₘ` | [`cutoff_relEntropy_radius`](Challenge.lean#L369) | [L412](Cutfast/CutoffRadius.lean#L412) |
| | `Iₘ` | [`cutoff_fisherInfo_radius`](Challenge.lean#L382) | [L431](Cutfast/CutoffRadius.lean#L431) |
| Theorem 1.2, radius `r d^θ` | `W₂²` | [`cutoff_fixedExponent_wassersteinSq_radius`](Challenge.lean#L394) | [L449](Cutfast/CutoffRadius.lean#L449) |
| | `Hₘ` | [`cutoff_fixedExponent_relEntropy_radius`](Challenge.lean#L405) | [L461](Cutfast/CutoffRadius.lean#L461) |
| | `Iₘ` | [`cutoff_fixedExponent_fisherInfo_radius`](Challenge.lean#L416) | [L473](Cutfast/CutoffRadius.lean#L473) |

- **Statement:** the paper's sentence "the mixing time would become `max(α/2, θ) log d`" (Theorem
  1.1, any `θ ∈ ℝ`) and "`θ log d`" (Theorem 1.2, `θ > 0`), stated as in Theorems 1.1 and 1.2.
- **Proof:** the same closed forms, with lower bounds on the dilation term for every `α`
  (`min(1,α) u ≤ 1 - (1-u)^α`), since for small `θ` the dilation term dominates even when `α < 1`.

## Section 2: Wasserstein distance

### Lemma 2.1 (position-scale transformations)
- **Lean:** [`wassersteinSq_map_affine`](Challenge.lean#L430) →
  [`wassersteinSq_map_affine'`](Cutfast/Wasserstein.lean#L244).
- **Statement:** for `μ` a probability measure with finite second moment and `A` a positive
  (symmetric positive semidefinite) operator,
  `W₂²(μ, (A· + h)_#μ) = ∫|(A-I)x|² dμ + 2⟨(A-I)m_μ, h⟩ + |h|²`. The term
  `Tr((A-I)² M_μ)` is written as `∫|(A-I)x|² dμ`; the covariance form (eq. (W2cov)) is not stated
  separately.
- **Proof:** without Brenier's theorem. The upper bound uses the coupling `(id, T)_#μ`. For the
  lower bound, `A` is regularized into `A + δI`; the Fenchel–Young inequality
  `2⟨x, Bw⟩ ≤ ⟨Bx, x⟩ + ⟨Bw, w⟩` bounds `|x - y|²` below by `f₁(x) + f₂(y)`, whose integral
  against any coupling only depends on the marginals; then `δ → 0`
  ([`lower_bound`](Cutfast/Wasserstein.lean#L97)).

### Lemma 2.2 (elliptic families)
- **Lean:** [`wassersteinSq_elliptic`](Challenge.lean#L445) →
  [`wassersteinSq_elliptic'`](Cutfast/Elliptic.lean#L214).
- **Statement:** both covariance matrices are assumed positive definite (the corrected paper only
  needs `Σ_μ` definite; `ERRATA.md`, item 4). Square roots are `CFC.sqrt` for the matrix order.
- **Proof:** as in the paper: `A = R⁻¹ √(R Σ_ν R) R⁻¹` with `R = √Σ_μ` satisfies `A Σ_μ A = Σ_ν`
  ([`transportMatrix_mul`](Cutfast/Elliptic.lean#L86)), so rotation invariance of `η` identifies
  `ν` as the image of `μ` under `x ↦ A(x - m_μ) + m_ν`; then Lemma 2.1, and the trace is computed
  from the covariance identity of `η`.

## Section 3: full-space Barenblatt profile (Lemma 3.1)

- **Lean:** [`fullBarenblatt_moment`](Challenge.lean#L476) (eq. (Bac)) →
  [`Moments.lean` L69](Cutfast/Moments.lean#L69);
  [`fullBarenblatt_integral_rpow`](Challenge.lean#L485) (eq. (Bm)) →
  [`Moments.lean` L104](Cutfast/Moments.lean#L104);
  [`fullBarenblatt_asymptotics`](Challenge.lean#L497) (eqs. (M2sim), (difference-fde)) →
  [`Asymptotics.lean` L417](Cutfast/Asymptotics.lean#L417).
- **Statement:** (Bac) for `-d < a < 2p - d` (corrected range, `ERRATA.md`, item 1). The
  asymptotics are stated for `p = dα/(2α-1)` and `b = (2α-1)/(2(α(d-2)+1))`, which is the profile
  `v_∞`.
- **Proof:** the exact formulas are eq. (Ba) of [`Radial.lean`](Cutfast/Radial.lean#L252) with the
  normalizing constant substituted. The asymptotics use a crude real Stirling formula
  `log Γ(x) = x log x - x + o(x)` ([`Asymptotics.lean` L97](Cutfast/Asymptotics.lean#L97)). The
  `O(1)` difference is in fact exactly `0` for large `d`
  ([`fullBarenblatt_secondMoment_eq`](Cutfast/Moments.lean#L206), virial identity).

## Section 4: compactly supported Barenblatt profile (Lemmas 4.1, 4.2)

- **Lean:** [`compactBarenblatt_moment`](Challenge.lean#L527) (eq. (CBac)) →
  [`Moments.lean` L139](Cutfast/Moments.lean#L139);
  [`compactBarenblatt_integral_rpow`](Challenge.lean#L538) (eq. (Bmpme)) →
  [`Moments.lean` L175](Cutfast/Moments.lean#L175);
  [`compactBarenblatt_asymptotics`](Challenge.lean#L550) (eqs. (limit-alpha-constant-pme),
  (difference-pme)) → [`Asymptotics.lean` L492](Cutfast/Asymptotics.lean#L492);
  [`compactBarenblatt_fixedExponent_asymptotics`](Challenge.lean#L566) (Lemma 4.2) →
  [`Asymptotics.lean` L554](Cutfast/Asymptotics.lean#L554);
  [`compactBarenblatt_support`](Challenge.lean#L578) (support radius, after Lemma 4.2) →
  [`CutoffRadius.lean` L485](Cutfast/CutoffRadius.lean#L485).
- **Statement:** (CBac) is proved for all `a > -d`, more than the paper's `a ≥ 0`; (Bmpme) needs
  `m > 0` (`ERRATA.md`, item 2). Lemma 4.2 is stated with `Asymptotics.IsEquivalent` (`~`).
- **Proof:** eq. (Baporous) of [`Radial.lean`](Cutfast/Radial.lean#L271) and the same Stirling
  estimates as for Lemma 3.1; again the `O(1)` difference is exactly `0`
  ([`compactBarenblatt_secondMoment_eq`](Cutfast/Moments.lean#L242)).

## Remark 3.2: Student t-distributions

All proofs reduce to the standard Student density by the change of variables `x = x₀ + √Σ y`
([`Student.lean`](Cutfast/Student.lean)).

| Claim | Lean statement | Proof | How |
|---|---|---|---|
| `x₀ + Y/√(Z/r)` has the Student density | [`student_law`](Challenge.lean#L607) | [L722](Cutfast/Student.lean#L722) | substitution `y = √(z/r) x`, Tonelli, Gamma integral; the Gaussian density comes from Mathlib's characteristic function |
| mean iff `r > 1` (`= x₀`), covariance iff `r > 2` (`= r/(r-2) Σ`) | [`student_moments`](Challenge.lean#L617) | [L745](Cutfast/Student.lean#L745) | radial integrals; the covariance by reflection invariance and polarization |
| `→ 𝒩(x₀, Σ)` as `r → ∞` | [`tendsto_student_gaussian`](Challenge.lean#L628) | [L878](Cutfast/Student.lean#L878) | dominated convergence for the unnormalized kernels; no Gamma asymptotics needed (`ERRATA.md`, item 10) |
| `(X-x₀)ᵀΣ⁻¹(X-x₀)/d ∼ F(d,r)`; isotropic case rotation invariant | [`student_fisherSnedecor`](Challenge.lean#L637) | [L1020](Cutfast/Student.lean#L1020) | radial image of the standard density under `y ↦ |y|²/d` (`ERRATA.md`, item 9) |
| `B` and `v_∞` are Student densities with `r = 1/(α(1-m))` (`m < 1`) | [`barenblatt_eq_student`](Challenge.lean#L648) | [L1168](Cutfast/Student.lean#L1168) | a normalized profile `(c + b|x|²)^{-(r+d)/2}` is an isotropic Student density |
| `m = (d-1)/d`: `r = d` and `σ_d² → 2πe` | [`barenblatt_student_dMinusOne`](Challenge.lean#L658) | [L1220](Cutfast/Student.lean#L1220) | `σ_d²` from `M₂ = d²σ_d²/(d-2)` and Lemma 3.1 |

## Remark 4.3: projections of uniform laws on spheres

`sphereUniform d R` is the normalized surface measure of the sphere of radius `R` (Mathlib's
`Measure.toSphere`, pushed forward by `x ↦ Rx`). All computations go through polar coordinates
and the Gaussian representation `∫ g dσ = ∫ g(x/|x|) γ(dx)` ([`Sphere.lean`](Cutfast/Sphere.lean)).

| Claim | Lean statement | Proof | How |
|---|---|---|---|
| `(X₁,…,X_n)` has density `C(R² - |y|²)^{(d-n-2)/2}` on the ball | [`sphereUniform_map_projFirst`](Challenge.lean#L681) | [L747](Cutfast/Sphere.lean#L747) | split `ℝ^{n+k} = ℝⁿ × ℝᵏ`, one-dimensional substitutions, Tonelli; corrected constant (`ERRATA.md`, items 8, 12, 14) |
| `RZ/|Z|` is uniform on the sphere | [`stdGaussian_map_sphereUniform`](Challenge.lean#L690) | [L756](Cutfast/Sphere.lean#L756) | the Gaussian density is radial, so polar coordinates separate the direction `Z/|Z|` from the radius |
| stereographic projection has density `Γ(d-1)/(π^{(d-1)/2} Γ((d-1)/2)) (1+|y|²)^{-(d-1)}` | [`sphereUniform_map_stereoProj`](Challenge.lean#L702) | [L763](Cutfast/Sphere.lean#L763) | substitution `t = (a² - λ²)/(2λ)` and Legendre duplication (`ERRATA.md`, item 11) |

The density in `sphereUniform_map_projFirst` is restricted to the open ball by an indicator: with
the `max (·) 0 ^ e` convention alone, the case `d = n + 2` would give the constant density `C` on
all of `ℝⁿ` (`0 ^ 0 = 1`), which is false
([`sphereUniform_map_projFirst_counterexample`](Cutfast/Sphere.lean#L502)).

## Not formalized

- Uniqueness of the solution of the PDE with Dirac initial data: the solution is the explicit
  formula, as in the paper, and it is proved to satisfy the equation where it is positive.
- Demange's spherical profile (Section 1.4.5), which would need the Laplace–Beltrami operator.
- The qualitative comments of Sections 1.4.1 and 1.4.4–1.4.6.
