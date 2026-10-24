module

public import Mathlib

@[expose] public section

/-!
# Cutoff phenomenon for fast diffusion and porous medium equations

Advertised statements of the formalization of the paper *On the cutoff phenomenon for fast
diffusion and porous medium equations* by D. Chafaï, M. Fathi and N. Simonov (arXiv:2503.11770;
corrected source `cutfast-lean.tex`). This file is the small, trusted statement
surface: every definition below has its ordinary mathematical meaning, documented in its
docstring, and the theorems state the results of the paper.

For a dimension `d` and an exponent `m > 0`, `m ≠ 1`, the paper considers the
Fokker–Planck version `∂ₜv = Δ(vᵐ) + div(x v)` of `∂ₜu = Δ(uᵐ)` with Dirac initial data at
`x₀ ∈ ℝᵈ`, whose solution is explicit (eq. (FDEFPv)):
`v(t,x) = s(t)^{-αd} B((x - e^{-t}x₀) / s(t)^α)` with `s(t) = α(1 - e^{-t/α})`,
`α = 1/(2 - d(1-m))`, and `B` the Barenblatt profile
`B(x) = (c + α(1-m)/(2m)|x|²)₊^{1/(m-1)}` normalized to be a probability density.
The equilibrium is `v_∞(x) = α^{-αd} B(x / α^α)` (eq. (vinf)).

The main results (Theorems 1.1 and 1.2 of the paper) state that, in high dimension, the
quadratic Wasserstein distance `W₂²`, the relative entropy `Hₘ` and the Fisher information
`Iₘ` between `v(t)` and `v_∞`, maximized over `|x₀| ≤ r√d`, collapse abruptly from `+∞`
to `0` around the critical time `max(1,α)/2 · log d` (resp. `1/2 · log d` for fixed `m > 1`).

The file also states the remaining mathematical claims of the paper: the solution `u` of
`∂ₜu = Δ(uᵐ)` and the time change linking it to `v`, the initial and long-time behavior, the
moment condition and the infinite Wasserstein distance for heavy tails, the entropy dissipation
identity, the Bregman form of the entropy, the diffusion limit `m → 1`, other sizes of the set of
initial points (Section 1.4.3), Lemmas 2.1–4.2, and Remarks 3.2 (Student t-distributions) and 4.3
(projections of uniform laws on spheres). Some claims of the paper are corrected here; see
`ERRATA.md`.
-/

open MeasureTheory Filter Topology Metric Real
open scoped ENNReal InnerProductSpace BoundedContinuousFunction MatrixOrder

namespace Cutfast

/-- The Euclidean space `ℝᵈ`. -/
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The exponent `α = 1 / (2 - d(1-m))` of the self-similar scaling (eq. (B)). -/
noncomputable def alpha (d : ℕ) (m : ℝ) : ℝ := 1 / (2 - d * (1 - m))

/-- The Barenblatt profile with a free constant `c`:
`B_c(x) = (c + α(1-m)/(2m) |x|²)₊ ^ (1/(m-1))` (eq. (B)). -/
noncomputable def barenblattWith (d : ℕ) (m c : ℝ) (x : E d) : ℝ :=
  (max (c + alpha d m * (1 - m) / (2 * m) * ‖x‖ ^ 2) 0) ^ (1 / (m - 1))

/-- The normalizing constant `c = c_{d,m} > 0` of the Barenblatt profile: a constant `c > 0`
such that `B_c` is a probability density function (it exists and is unique, see
`barenblattConst_spec`); the junk value `0` is used if there is none. -/
noncomputable def barenblattConst (d : ℕ) (m : ℝ) : ℝ :=
  open Classical in
  if h : ∃ c : ℝ, 0 < c ∧ Integrable (barenblattWith d m c) ∧ ∫ x, barenblattWith d m c x = 1
  then h.choose else 0

/-- The Barenblatt probability density function `B = B_{c_{d,m}}` (eq. (B)). -/
noncomputable def barenblatt (d : ℕ) (m : ℝ) (x : E d) : ℝ :=
  barenblattWith d m (barenblattConst d m) x

/-- The solution `v(t,x)` of the Fokker–Planck fast diffusion / porous medium equation
`∂ₜv = Δ(vᵐ) + div(x v)` with initial condition `δ_{x₀}` (eq. (FDEFPv)):
`v(t,x) = (α(1-e^{-t/α}))^{-αd} B((x - e^{-t}x₀) / (α(1-e^{-t/α}))^α)`. -/
noncomputable def solution (d : ℕ) (m : ℝ) (x₀ : E d) (t : ℝ) (x : E d) : ℝ :=
  ((alpha d m * (1 - exp (-t / alpha d m))) ^ (alpha d m * d))⁻¹ *
    barenblatt d m (((alpha d m * (1 - exp (-t / alpha d m))) ^ alpha d m)⁻¹ •
      (x - exp (-t) • x₀))

/-- The equilibrium `v_∞(x) = lim_{t→∞} v(t,x) = α^{-αd} B(x / α^α)` (eq. (vinf)). -/
noncomputable def equilibrium (d : ℕ) (m : ℝ) (x : E d) : ℝ :=
  (alpha d m ^ (alpha d m * d))⁻¹ * barenblatt d m ((alpha d m ^ alpha d m)⁻¹ • x)

/-- The measure `f(x) dx` with density `f` with respect to the Lebesgue measure of `ℝᵈ`. -/
noncomputable def densityMeasure {d : ℕ} (f : E d → ℝ) : Measure (E d) :=
  volume.withDensity fun x => ENNReal.ofReal (f x)

/-- The squared quadratic Monge–Kantorovich–Wasserstein distance
`W₂²(μ,ν) = inf_π ∫ |x-y|² dπ(x,y)`, the infimum over all couplings `γ` of `μ` and `ν`
(probability measures on `ℝᵈ × ℝᵈ` with marginals `μ` and `ν`), with values in `[0,∞]`. -/
noncomputable def wassersteinSq {d : ℕ} (μ ν : Measure (E d)) : ℝ≥0∞ :=
  ⨅ (γ : Measure (E d × E d)) (_ : IsProbabilityMeasure γ)
    (_ : γ.map Prod.fst = μ) (_ : γ.map Prod.snd = ν), ∫⁻ p, edist p.1 p.2 ^ 2 ∂γ

/-- The integrand of the relative entropy (free energy) `Hₘ(f | g)` of eq. (tsalis):
`(f(x)ᵐ - g(x)ᵐ - (1-m)/2 |x|² (f(x) - g(x))) / (m-1)`. -/
noncomputable def relEntropyDensity {d : ℕ} (m : ℝ) (f g : E d → ℝ) (x : E d) : ℝ :=
  (f x ^ m - g x ^ m - (1 - m) / 2 * ‖x‖ ^ 2 * (f x - g x)) / (m - 1)

/-- The relative entropy (free energy) of eq. (tsalis):
`Hₘ(f | g) = 1/(m-1) ∫ (f(x)ᵐ - g(x)ᵐ - (1-m)/2 |x|² (f(x) - g(x))) dx`. -/
noncomputable def relEntropy {d : ℕ} (m : ℝ) (f g : E d → ℝ) : ℝ :=
  ∫ x, relEntropyDensity m f g x

/-- The Fisher information (entropy production) of eq. (fisher), relative to the
equilibrium `v_∞` (which enters through the confinement `x`):
`Iₘ(f | v_∞) = ∫ f(x) |x + m/(m-1) ∇(f^{m-1})(x)|² dx`, with values in `[0,∞]`. -/
noncomputable def fisherInfo {d : ℕ} (m : ℝ) (f : E d → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (f x * ‖x + (m / (m - 1)) • gradient (fun y => f y ^ (m - 1)) x‖ ^ 2)

/-- The exponent `m = ((d-2)α + 1)/(dα)` attached to a fixed `α` in dimension `d`
(Theorem 1.1); equivalently `α = 1/(2 - d(1-m))`. -/
noncomputable def exponentOfAlpha (α : ℝ) (d : ℕ) : ℝ := ((d - 2) * α + 1) / (d * α)

/-! ## The Barenblatt profile and the solution -/

/-- The normalizing constant of the Barenblatt profile exists and is unique: for `d ≥ 1`,
`m > 0`, `m ≠ 1` and `m > (d-2)/d`, `c_{d,m}` is the unique `c > 0` making `B_c` a
probability density function. -/
theorem barenblattConst_spec {d : ℕ} {m : ℝ} (hd : 1 ≤ d) (hm0 : 0 < m) (hm1 : m ≠ 1)
    (hmd : ((d : ℝ) - 2) / d < m) :
    0 < barenblattConst d m ∧ Integrable (barenblattWith d m (barenblattConst d m)) ∧
      ∫ x, barenblattWith d m (barenblattConst d m) x = 1 ∧
      ∀ c : ℝ, 0 < c → Integrable (barenblattWith d m c) →
        ∫ x, barenblattWith d m c x = 1 → c = barenblattConst d m := by
  sorry

/-- For every time `t > 0`, `v(t,·)` is a probability density function. -/
theorem solution_isProbabilityDensity {d : ℕ} {m : ℝ} (hd : 1 ≤ d) (hm0 : 0 < m)
    (hm1 : m ≠ 1) (hmd : ((d : ℝ) - 2) / d < m) (x₀ : E d) {t : ℝ} (ht : 0 < t) :
    (∀ x, 0 ≤ solution d m x₀ t x) ∧ IsProbabilityMeasure (densityMeasure (solution d m x₀ t)) := by
  sorry

/-- `v_∞` is a probability density function. -/
theorem equilibrium_isProbabilityDensity {d : ℕ} {m : ℝ} (hd : 1 ≤ d) (hm0 : 0 < m)
    (hm1 : m ≠ 1) (hmd : ((d : ℝ) - 2) / d < m) :
    (∀ x, 0 ≤ equilibrium d m x) ∧ IsProbabilityMeasure (densityMeasure (equilibrium d m)) := by
  sorry

/-- `v` solves the Fokker–Planck equation `∂ₜv = Δ(vᵐ) + div(x v)` (eq. (FDEFP)), written as
`∂ₜv = Δ(vᵐ) + d v + ⟨x, ∇v⟩`, at every point `(t,x)`, `t > 0`, of positivity of `v`
(this is everywhere when `m < 1`). -/
theorem solution_hasDerivAt {d : ℕ} {m : ℝ} (hd : 1 ≤ d) (hm0 : 0 < m) (hm1 : m ≠ 1)
    (hmd : ((d : ℝ) - 2) / d < m) (x₀ : E d) {t : ℝ} (ht : 0 < t) {x : E d}
    (hx : 0 < solution d m x₀ t x) :
    HasDerivAt (fun s => solution d m x₀ s x)
      (Laplacian.laplacian (fun y => solution d m x₀ t y ^ m) x +
        d * solution d m x₀ t x + ⟪x, gradient (solution d m x₀ t) x⟫_ℝ) t := by
  sorry

/-! ## Section 1.2: the equation `∂ₜu = Δ(uᵐ)`, the time change, initial and long-time behavior -/

/-- The solution `u(t,x) = t^{-αd} B((x - x₀)/t^α)` of `∂ₜu = Δ(uᵐ)` with `u(0,·) = δ_{x₀}`
(eq. (sol)). -/
noncomputable def fdeSolution (d : ℕ) (m : ℝ) (x₀ : E d) (t : ℝ) (x : E d) : ℝ :=
  (t ^ (alpha d m * d))⁻¹ * barenblatt d m ((t ^ alpha d m)⁻¹ • (x - x₀))

/-- `u` solves `∂ₜu = Δ(uᵐ)` (eq. (FDE)) at every point `(t,x)`, `t > 0`, of positivity of `u`. -/
theorem fdeSolution_hasDerivAt {d : ℕ} {m : ℝ} (hd : 1 ≤ d) (hm0 : 0 < m) (hm1 : m ≠ 1)
    (hmd : ((d : ℝ) - 2) / d < m) (x₀ : E d) {t : ℝ} (ht : 0 < t) {x : E d}
    (hx : 0 < fdeSolution d m x₀ t x) :
    HasDerivAt (fun s => fdeSolution d m x₀ s x)
      (Laplacian.laplacian (fun y => fdeSolution d m x₀ t y ^ m) x) t := by
  sorry

/-- For every `t > 0`, `u(t,·)` is a probability density function (positivity and mass are
preserved). -/
theorem fdeSolution_isProbabilityDensity {d : ℕ} {m : ℝ} (hd : 1 ≤ d) (hm0 : 0 < m)
    (hm1 : m ≠ 1) (hmd : ((d : ℝ) - 2) / d < m) (x₀ : E d) {t : ℝ} (ht : 0 < t) :
    (∀ x, 0 ≤ fdeSolution d m x₀ t x) ∧
      IsProbabilityMeasure (densityMeasure (fdeSolution d m x₀ t)) := by
  sorry

/-- The time change (eqs. (uv) and (FDEFPv)): `v(t,x) = e^{dt} u(α(e^{t/α} - 1), eᵗx)`. -/
theorem solution_eq_fdeSolution {d : ℕ} {m : ℝ} (hd : 1 ≤ d) (hm0 : 0 < m) (hm1 : m ≠ 1)
    (hmd : ((d : ℝ) - 2) / d < m) (x₀ : E d) {t : ℝ} (ht : 0 < t) (x : E d) :
    solution d m x₀ t x =
      exp (d * t) * fdeSolution d m x₀ (alpha d m * (exp (t / alpha d m) - 1)) (exp t • x) := by
  sorry

/-- Initial condition: `u(t,·) → δ_{x₀}` weakly as `t → 0⁺`. -/
theorem tendsto_fdeSolution_zero {d : ℕ} {m : ℝ} (hd : 1 ≤ d) (hm0 : 0 < m) (hm1 : m ≠ 1)
    (hmd : ((d : ℝ) - 2) / d < m) (x₀ : E d) (φ : E d →ᵇ ℝ) :
    Tendsto (fun t => ∫ x, φ x * fdeSolution d m x₀ t x) (𝓝[>] 0) (𝓝 (φ x₀)) := by
  sorry

/-- Initial condition: `v(t,·) → δ_{x₀}` weakly as `t → 0⁺`. -/
theorem tendsto_solution_zero {d : ℕ} {m : ℝ} (hd : 1 ≤ d) (hm0 : 0 < m) (hm1 : m ≠ 1)
    (hmd : ((d : ℝ) - 2) / d < m) (x₀ : E d) (φ : E d →ᵇ ℝ) :
    Tendsto (fun t => ∫ x, φ x * solution d m x₀ t x) (𝓝[>] 0) (𝓝 (φ x₀)) := by
  sorry

/-- Long-time behavior (eq. (vinf)): `v(t,x) → v_∞(x)` as `t → ∞`, and
`v_∞(x) = (C + (1-m)/(2m)|x|²)₊^{1/(m-1)}` for some constant `C > 0`. -/
theorem tendsto_solution_atTop {d : ℕ} {m : ℝ} (hd : 1 ≤ d) (hm0 : 0 < m) (hm1 : m ≠ 1)
    (hmd : ((d : ℝ) - 2) / d < m) (x₀ : E d) :
    (∀ x, Tendsto (fun t => solution d m x₀ t x) atTop (𝓝 (equilibrium d m x))) ∧
    ∃ C : ℝ, 0 < C ∧ ∀ x, equilibrium d m x = (max (C + (1 - m) / (2 * m) * ‖x‖ ^ 2) 0) ^ (1 / (m - 1)) := by
  sorry

/-- `v_∞` has a finite second moment if and only if `m > d/(d+2)` (Section 1.2). -/
theorem integrable_sq_mul_equilibrium_iff {d : ℕ} {m : ℝ} (hd : 1 ≤ d) (hm0 : 0 < m)
    (hm1 : m ≠ 1) (hmd : ((d : ℝ) - 2) / d < m) :
    Integrable (fun x => ‖x‖ ^ 2 * equilibrium d m x) ↔ (d : ℝ) / (d + 2) < m := by
  sorry

/-- When `(d-2)/d < m ≤ d/(d+2)`, the Wasserstein distance between `v(t)` and `v_∞` is infinite
for every `t > 0` (Section 1.3). -/
theorem wassersteinSq_eq_top {d : ℕ} {m : ℝ} (hd : 1 ≤ d) (hm0 : 0 < m)
    (hmd : ((d : ℝ) - 2) / d < m) (hm2 : m ≤ (d : ℝ) / (d + 2)) (x₀ : E d) {t : ℝ} (ht : 0 < t) :
    wassersteinSq (densityMeasure (solution d m x₀ t)) (densityMeasure (equilibrium d m)) = ⊤ := by
  sorry

/-! ## Section 1.3: relative entropy and Fisher information -/

/-- The entropy dissipation identity `d/dt Hₘ(v(t) | v_∞) = -Iₘ(v(t) | v_∞)` along the solution
(the Fisher information is finite). -/
theorem relEntropy_hasDerivAt {d : ℕ} {m : ℝ} (hd : 1 ≤ d) (hm0 : 0 < m) (hm1 : m ≠ 1)
    (hmd : ((d : ℝ) - 2) / d < m) (h2 : (d : ℝ) / (d + 2) < m) (x₀ : E d) {t : ℝ} (ht : 0 < t) :
    fisherInfo m (solution d m x₀ t) ≠ ⊤ ∧
    HasDerivAt (fun s => relEntropy m (solution d m x₀ s) (equilibrium d m))
      (-(fisherInfo m (solution d m x₀ t)).toReal) t := by
  sorry

/-- The Bregman form of the relative entropy (eq. (tsalisbis)): for a probability density `f`
with finite second moment and `fᵐ` integrable, which vanishes outside the support of `v_∞` when
`m > 1`, `Hₘ(f | v_∞) = 1/(m-1) ∫ (fᵐ - v_∞ᵐ - m v_∞^{m-1} (f - v_∞))`, and this is `≥ 0`. -/
theorem relEntropy_eq_bregman {d : ℕ} {m : ℝ} (hd : 1 ≤ d) (hm0 : 0 < m) (hm1 : m ≠ 1)
    (hmd : ((d : ℝ) - 2) / d < m) (h2 : (d : ℝ) / (d + 2) < m) (f : E d → ℝ)
    (hf0 : ∀ x, 0 ≤ f x) (hf : Integrable f) (hf1 : ∫ x, f x = 1)
    (hfm : Integrable fun x => f x ^ m) (hf2 : Integrable fun x => ‖x‖ ^ 2 * f x)
    (hsupp : 1 < m → ∀ x, equilibrium d m x = 0 → f x = 0) :
    Integrable (relEntropyDensity m f (equilibrium d m)) ∧
    relEntropy m f (equilibrium d m) =
      ∫ x, (f x ^ m - equilibrium d m x ^ m -
        m * equilibrium d m x ^ (m - 1) * (f x - equilibrium d m x)) / (m - 1) ∧
    0 ≤ relEntropy m f (equilibrium d m) := by
  sorry

/-- `x ↦ (xᵐ - 1)/(m - 1)` is strictly convex on `[0,∞)` for `m > 0`, `m ≠ 1`, and, up to the
affine term `(x - 1)/(m - 1)` (whose integral vanishes between probability densities), it gives
the classical entropy as `m → 1`: `(xᵐ - x)/(m - 1) → x log x` (Section 1.3). -/
theorem tsallis_strictConvexOn_tendsto_log {m : ℝ} (hm0 : 0 < m) (hm1 : m ≠ 1) :
    StrictConvexOn ℝ (Set.Ici 0) (fun x : ℝ => (x ^ m - 1) / (m - 1)) ∧
    ∀ x : ℝ, 0 < x → Tendsto (fun m : ℝ => (x ^ m - x) / (m - 1)) (𝓝[≠] 1) (𝓝 (x * log x)) := by
  sorry

/-! ## Section 1.4.2: diffusion limit `m → 1` -/

/-- Diffusion limit (Section 1.4.2): as `m → 1` at fixed `d`, `B(x) → (4π)^{-d/2} e^{-|x|²/4}`. -/
theorem tendsto_barenblatt_one {d : ℕ} (hd : 1 ≤ d) (x : E d) :
    Tendsto (fun m => barenblatt d m x) (𝓝[≠] 1)
      (𝓝 ((4 * π) ^ (-(d : ℝ) / 2) * exp (-‖x‖ ^ 2 / 4))) := by
  sorry

/-- Diffusion limit, heat kernel (eq. (heatkernel)): as `m → 1`,
`u(t,x) → (4πt)^{-d/2} e^{-|x-x₀|²/(4t)}`. -/
theorem tendsto_fdeSolution_one {d : ℕ} (hd : 1 ≤ d) (x₀ : E d) {t : ℝ} (ht : 0 < t)
    (x : E d) :
    Tendsto (fun m => fdeSolution d m x₀ t x) (𝓝[≠] 1)
      (𝓝 ((4 * π * t) ^ (-(d : ℝ) / 2) * exp (-‖x - x₀‖ ^ 2 / (4 * t)))) := by
  sorry

/-- Diffusion limit, Mehler formula: as `m → 1`, `v(t,·)` tends pointwise to the density of
`𝒩(e^{-t}x₀, (1-e^{-2t}) I)`. -/
theorem tendsto_solution_one {d : ℕ} (hd : 1 ≤ d) (x₀ : E d) {t : ℝ} (ht : 0 < t) (x : E d) :
    Tendsto (fun m => solution d m x₀ t x) (𝓝[≠] 1)
      (𝓝 ((2 * π * (1 - exp (-2 * t))) ^ (-(d : ℝ) / 2) *
        exp (-‖x - exp (-t) • x₀‖ ^ 2 / (2 * (1 - exp (-2 * t)))))) := by
  sorry

/-! ## Theorem 1.1: cutoff phenomenon for fixed `α` -/

/-- **Theorem 1.1, Wasserstein distance.** Fix `α ∈ (0,1/2) ∪ (1/2,∞)`, `r > 0`, and let
`m = ((d-2)α+1)/(dα)`. Then `sup_{|x₀| ≤ r√d} W₂²(v(t_d), v_∞)` tends to `+∞` if
`t_d = (1-ε) max(1,α)/2 log d` and to `0` if `t_d = (1+ε) max(1,α)/2 log d`. -/
theorem cutoff_wassersteinSq {α r ε : ℝ} (hα : 0 < α) (hα2 : α ≠ 1 / 2) (hr : 0 < r)
    (hε : 0 < ε) :
    (ε < 1 → Tendsto (fun d : ℕ => ⨆ x₀ ∈ closedBall (0 : E d) (r * √d),
        wassersteinSq
          (densityMeasure (solution d (exponentOfAlpha α d) x₀ ((1 - ε) * (max 1 α / 2) * log d)))
          (densityMeasure (equilibrium d (exponentOfAlpha α d)))) atTop (𝓝 ⊤)) ∧
    Tendsto (fun d : ℕ => ⨆ x₀ ∈ closedBall (0 : E d) (r * √d),
        wassersteinSq
          (densityMeasure (solution d (exponentOfAlpha α d) x₀ ((1 + ε) * (max 1 α / 2) * log d)))
          (densityMeasure (equilibrium d (exponentOfAlpha α d)))) atTop (𝓝 0) := by
  sorry

/-- **Theorem 1.1, relative entropy.** Same setting as `cutoff_wassersteinSq`. For large `d`
the entropy integrand is integrable for all `t > 0` and `|x₀| ≤ r√d`, and
`sup_{|x₀| ≤ r√d} Hₘ(v(t_d) | v_∞)` tends to `+∞` if `t_d = (1-ε) max(1,α)/2 log d`
and to `0` if `t_d = (1+ε) max(1,α)/2 log d`. -/
theorem cutoff_relEntropy {α r ε : ℝ} (hα : 0 < α) (hα2 : α ≠ 1 / 2) (hr : 0 < r)
    (hε : 0 < ε) :
    (∀ᶠ d : ℕ in atTop, ∀ x₀ ∈ closedBall (0 : E d) (r * √d), ∀ t > 0,
      Integrable (relEntropyDensity (exponentOfAlpha α d) (solution d (exponentOfAlpha α d) x₀ t)
        (equilibrium d (exponentOfAlpha α d)))) ∧
    (ε < 1 → Tendsto (fun d : ℕ => ⨆ x₀ ∈ closedBall (0 : E d) (r * √d),
        (relEntropy (exponentOfAlpha α d)
          (solution d (exponentOfAlpha α d) x₀ ((1 - ε) * (max 1 α / 2) * log d))
          (equilibrium d (exponentOfAlpha α d)) : EReal)) atTop (𝓝 ⊤)) ∧
    Tendsto (fun d : ℕ => ⨆ x₀ ∈ closedBall (0 : E d) (r * √d),
        (relEntropy (exponentOfAlpha α d)
          (solution d (exponentOfAlpha α d) x₀ ((1 + ε) * (max 1 α / 2) * log d))
          (equilibrium d (exponentOfAlpha α d)) : EReal)) atTop (𝓝 0) := by
  sorry

/-- **Theorem 1.1, Fisher information.** Same setting as `cutoff_wassersteinSq`:
`sup_{|x₀| ≤ r√d} Iₘ(v(t_d) | v_∞)` tends to `+∞` if `t_d = (1-ε) max(1,α)/2 log d`
and to `0` if `t_d = (1+ε) max(1,α)/2 log d`. -/
theorem cutoff_fisherInfo {α r ε : ℝ} (hα : 0 < α) (hα2 : α ≠ 1 / 2) (hr : 0 < r)
    (hε : 0 < ε) :
    (ε < 1 → Tendsto (fun d : ℕ => ⨆ x₀ ∈ closedBall (0 : E d) (r * √d),
        fisherInfo (exponentOfAlpha α d)
          (solution d (exponentOfAlpha α d) x₀ ((1 - ε) * (max 1 α / 2) * log d))) atTop (𝓝 ⊤)) ∧
    Tendsto (fun d : ℕ => ⨆ x₀ ∈ closedBall (0 : E d) (r * √d),
        fisherInfo (exponentOfAlpha α d)
          (solution d (exponentOfAlpha α d) x₀ ((1 + ε) * (max 1 α / 2) * log d))) atTop (𝓝 0) := by
  sorry

/-! ## Theorem 1.2: cutoff phenomenon for a fixed exponent `m > 1` -/

/-- **Theorem 1.2, Wasserstein distance.** Fix `m > 1` and `r > 0` (so that
`α = 1/(2 - d(1-m)) → 0`). Then `sup_{|x₀| ≤ r√d} W₂²(v(t_d), v_∞)` tends to `+∞` if
`t_d = (1-ε)/2 log d` and to `0` if `t_d = (1+ε)/2 log d`. -/
theorem cutoff_fixedExponent_wassersteinSq {m r ε : ℝ} (hm : 1 < m) (hr : 0 < r)
    (hε : 0 < ε) :
    (ε < 1 → Tendsto (fun d : ℕ => ⨆ x₀ ∈ closedBall (0 : E d) (r * √d),
        wassersteinSq (densityMeasure (solution d m x₀ ((1 - ε) / 2 * log d)))
          (densityMeasure (equilibrium d m))) atTop (𝓝 ⊤)) ∧
    Tendsto (fun d : ℕ => ⨆ x₀ ∈ closedBall (0 : E d) (r * √d),
        wassersteinSq (densityMeasure (solution d m x₀ ((1 + ε) / 2 * log d)))
          (densityMeasure (equilibrium d m))) atTop (𝓝 0) := by
  sorry

/-- **Theorem 1.2, relative entropy.** Same setting as `cutoff_fixedExponent_wassersteinSq`,
with integrability of the entropy integrand for large `d`. -/
theorem cutoff_fixedExponent_relEntropy {m r ε : ℝ} (hm : 1 < m) (hr : 0 < r) (hε : 0 < ε) :
    (∀ᶠ d : ℕ in atTop, ∀ x₀ ∈ closedBall (0 : E d) (r * √d), ∀ t > 0,
      Integrable (relEntropyDensity m (solution d m x₀ t) (equilibrium d m))) ∧
    (ε < 1 → Tendsto (fun d : ℕ => ⨆ x₀ ∈ closedBall (0 : E d) (r * √d),
        (relEntropy m (solution d m x₀ ((1 - ε) / 2 * log d)) (equilibrium d m) : EReal))
        atTop (𝓝 ⊤)) ∧
    Tendsto (fun d : ℕ => ⨆ x₀ ∈ closedBall (0 : E d) (r * √d),
        (relEntropy m (solution d m x₀ ((1 + ε) / 2 * log d)) (equilibrium d m) : EReal))
        atTop (𝓝 0) := by
  sorry

/-- **Theorem 1.2, Fisher information.** Same setting as
`cutoff_fixedExponent_wassersteinSq`. -/
theorem cutoff_fixedExponent_fisherInfo {m r ε : ℝ} (hm : 1 < m) (hr : 0 < r) (hε : 0 < ε) :
    (ε < 1 → Tendsto (fun d : ℕ => ⨆ x₀ ∈ closedBall (0 : E d) (r * √d),
        fisherInfo m (solution d m x₀ ((1 - ε) / 2 * log d))) atTop (𝓝 ⊤)) ∧
    Tendsto (fun d : ℕ => ⨆ x₀ ∈ closedBall (0 : E d) (r * √d),
        fisherInfo m (solution d m x₀ ((1 + ε) / 2 * log d))) atTop (𝓝 0) := by
  sorry

/-! ## Section 1.4.3: other sizes of the set of initial points -/

/-- **Section 1.4.3, Theorem 1.1 for other initial data, Wasserstein.** For initial points in the
ball of radius `r d^θ` (`θ ∈ ℝ`), the critical time becomes `max(α/2, θ) log d`. -/
theorem cutoff_wassersteinSq_radius {α r ε θ : ℝ} (hα : 0 < α) (hα2 : α ≠ 1 / 2) (hr : 0 < r)
    (hε : 0 < ε) :
    (ε < 1 → Tendsto (fun d : ℕ => ⨆ x₀ ∈ closedBall (0 : E d) (r * (d : ℝ) ^ θ),
        wassersteinSq
          (densityMeasure (solution d (exponentOfAlpha α d) x₀ ((1 - ε) * max (α / 2) θ * log d)))
          (densityMeasure (equilibrium d (exponentOfAlpha α d)))) atTop (𝓝 ⊤)) ∧
    Tendsto (fun d : ℕ => ⨆ x₀ ∈ closedBall (0 : E d) (r * (d : ℝ) ^ θ),
        wassersteinSq
          (densityMeasure (solution d (exponentOfAlpha α d) x₀ ((1 + ε) * max (α / 2) θ * log d)))
          (densityMeasure (equilibrium d (exponentOfAlpha α d)))) atTop (𝓝 0) := by
  sorry

/-- **Section 1.4.3, Theorem 1.1 for other initial data, relative entropy.** -/
theorem cutoff_relEntropy_radius {α r ε θ : ℝ} (hα : 0 < α) (hα2 : α ≠ 1 / 2) (hr : 0 < r)
    (hε : 0 < ε) :
    (ε < 1 → Tendsto (fun d : ℕ => ⨆ x₀ ∈ closedBall (0 : E d) (r * (d : ℝ) ^ θ),
        (relEntropy (exponentOfAlpha α d)
          (solution d (exponentOfAlpha α d) x₀ ((1 - ε) * max (α / 2) θ * log d))
          (equilibrium d (exponentOfAlpha α d)) : EReal)) atTop (𝓝 ⊤)) ∧
    Tendsto (fun d : ℕ => ⨆ x₀ ∈ closedBall (0 : E d) (r * (d : ℝ) ^ θ),
        (relEntropy (exponentOfAlpha α d)
          (solution d (exponentOfAlpha α d) x₀ ((1 + ε) * max (α / 2) θ * log d))
          (equilibrium d (exponentOfAlpha α d)) : EReal)) atTop (𝓝 0) := by
  sorry

/-- **Section 1.4.3, Theorem 1.1 for other initial data, Fisher information.** -/
theorem cutoff_fisherInfo_radius {α r ε θ : ℝ} (hα : 0 < α) (hα2 : α ≠ 1 / 2) (hr : 0 < r)
    (hε : 0 < ε) :
    (ε < 1 → Tendsto (fun d : ℕ => ⨆ x₀ ∈ closedBall (0 : E d) (r * (d : ℝ) ^ θ),
        fisherInfo (exponentOfAlpha α d)
          (solution d (exponentOfAlpha α d) x₀ ((1 - ε) * max (α / 2) θ * log d))) atTop (𝓝 ⊤)) ∧
    Tendsto (fun d : ℕ => ⨆ x₀ ∈ closedBall (0 : E d) (r * (d : ℝ) ^ θ),
        fisherInfo (exponentOfAlpha α d)
          (solution d (exponentOfAlpha α d) x₀ ((1 + ε) * max (α / 2) θ * log d))) atTop (𝓝 0) := by
  sorry

/-- **Section 1.4.3, Theorem 1.2 for other initial data, Wasserstein.** For initial points in the
ball of radius `r d^θ` (`θ > 0`), the critical time becomes `θ log d`. -/
theorem cutoff_fixedExponent_wassersteinSq_radius {m r ε θ : ℝ} (hm : 1 < m) (hr : 0 < r)
    (hε : 0 < ε) (hθ : 0 < θ) :
    (ε < 1 → Tendsto (fun d : ℕ => ⨆ x₀ ∈ closedBall (0 : E d) (r * (d : ℝ) ^ θ),
        wassersteinSq (densityMeasure (solution d m x₀ ((1 - ε) * θ * log d)))
          (densityMeasure (equilibrium d m))) atTop (𝓝 ⊤)) ∧
    Tendsto (fun d : ℕ => ⨆ x₀ ∈ closedBall (0 : E d) (r * (d : ℝ) ^ θ),
        wassersteinSq (densityMeasure (solution d m x₀ ((1 + ε) * θ * log d)))
          (densityMeasure (equilibrium d m))) atTop (𝓝 0) := by
  sorry

/-- **Section 1.4.3, Theorem 1.2 for other initial data, relative entropy.** -/
theorem cutoff_fixedExponent_relEntropy_radius {m r ε θ : ℝ} (hm : 1 < m) (hr : 0 < r)
    (hε : 0 < ε) (hθ : 0 < θ) :
    (ε < 1 → Tendsto (fun d : ℕ => ⨆ x₀ ∈ closedBall (0 : E d) (r * (d : ℝ) ^ θ),
        (relEntropy m (solution d m x₀ ((1 - ε) * θ * log d)) (equilibrium d m) : EReal))
        atTop (𝓝 ⊤)) ∧
    Tendsto (fun d : ℕ => ⨆ x₀ ∈ closedBall (0 : E d) (r * (d : ℝ) ^ θ),
        (relEntropy m (solution d m x₀ ((1 + ε) * θ * log d)) (equilibrium d m) : EReal))
        atTop (𝓝 0) := by
  sorry

/-- **Section 1.4.3, Theorem 1.2 for other initial data, Fisher information.** -/
theorem cutoff_fixedExponent_fisherInfo_radius {m r ε θ : ℝ} (hm : 1 < m) (hr : 0 < r)
    (hε : 0 < ε) (hθ : 0 < θ) :
    (ε < 1 → Tendsto (fun d : ℕ => ⨆ x₀ ∈ closedBall (0 : E d) (r * (d : ℝ) ^ θ),
        fisherInfo m (solution d m x₀ ((1 - ε) * θ * log d))) atTop (𝓝 ⊤)) ∧
    Tendsto (fun d : ℕ => ⨆ x₀ ∈ closedBall (0 : E d) (r * (d : ℝ) ^ θ),
        fisherInfo m (solution d m x₀ ((1 + ε) * θ * log d))) atTop (𝓝 0) := by
  sorry

/-! ## Lemma 2.1: Wasserstein distance for position-scale transformations -/

/-- **Lemma 2.1.** If `μ` is a probability measure on `ℝᵈ` with finite second moment and `ν`
is its image by `x ↦ Ax + h` with `A` symmetric positive semidefinite, then
`W₂²(μ,ν) = Tr((A-I)² M_μ) + 2⟨(A-I) m_μ, h⟩ + |h|²`, where `m_μ = ∫ x dμ` and
`Tr((A-I)² M_μ) = ∫ |(A-I)x|² dμ(x)` with `M_μ = ∫ x xᵀ dμ`. -/
theorem wassersteinSq_map_affine {d : ℕ} (μ : Measure (E d)) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x => ‖x‖ ^ 2) μ) (A : E d →L[ℝ] E d) (hA : A.IsPositive) (h : E d) :
    wassersteinSq μ (μ.map fun x => A x + h) =
      ENNReal.ofReal (∫ x, ‖(A - 1) x‖ ^ 2 ∂μ + 2 * ⟪(A - 1) (∫ x, x ∂μ), h⟫_ℝ + ‖h‖ ^ 2) := by
  sorry

/-! ## Lemma 2.2: Wasserstein distance for elliptic families -/

/-- **Lemma 2.2.** Let `η` be a rotationally invariant probability measure on `ℝᵈ` with finite
second moment, zero mean and identity covariance, and let `μ`, `ν` be its images under
`x ↦ m_μ + √Σ_μ x` and `x ↦ m_ν + √Σ_ν x`, with `Σ_μ`, `Σ_ν` symmetric positive definite
matrices. Then `μ`, `ν` have means `m_μ`, `m_ν` and covariances `Σ_μ`, `Σ_ν`, and
`W₂²(μ,ν) = Tr(Σ_μ + Σ_ν - 2 √(√Σ_μ Σ_ν √Σ_μ)) + |m_μ - m_ν|²`; if moreover `Σ_μ` and `Σ_ν`
commute, `W₂²(μ,ν) = Tr((√Σ_μ - √Σ_ν)²) + |m_μ - m_ν|²`. Square roots are those of the
continuous functional calculus (`CFC.sqrt`) for the order on matrices. -/
theorem wassersteinSq_elliptic {d : ℕ} (η : Measure (E d)) [IsProbabilityMeasure η]
    (hrot : ∀ U : E d ≃ₗᵢ[ℝ] E d, η.map U = η) (h2 : Integrable (fun x => ‖x‖ ^ 2) η)
    (hmean : ∫ x, x ∂η = 0) (hcov : ∀ u v : E d, ∫ x, ⟪x, u⟫_ℝ * ⟪x, v⟫_ℝ ∂η = ⟪u, v⟫_ℝ)
    (mμ mν : E d) (Sμ Sν : Matrix (Fin d) (Fin d) ℝ) (hSμ : Sμ.PosDef) (hSν : Sν.PosDef) :
    let μ := η.map fun x => mμ + Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt Sμ) x
    let ν := η.map fun x => mν + Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt Sν) x
    (∫ x, x ∂μ = mμ ∧ ∀ u v : E d, ∫ x, ⟪x - mμ, u⟫_ℝ * ⟪x - mμ, v⟫_ℝ ∂μ =
        ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) Sμ v⟫_ℝ) ∧
    (∫ x, x ∂ν = mν ∧ ∀ u v : E d, ∫ x, ⟪x - mν, u⟫_ℝ * ⟪x - mν, v⟫_ℝ ∂ν =
        ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) Sν v⟫_ℝ) ∧
    wassersteinSq μ ν = ENNReal.ofReal
      ((Sμ + Sν - 2 * CFC.sqrt (CFC.sqrt Sμ * Sν * CFC.sqrt Sμ)).trace + ‖mμ - mν‖ ^ 2) ∧
    (Sμ * Sν = Sν * Sμ → wassersteinSq μ ν = ENNReal.ofReal
      (((CFC.sqrt Sμ - CFC.sqrt Sν) ^ 2).trace + ‖mμ - mν‖ ^ 2)) := by
  sorry

/-! ## Lemma 3.1: full-space Barenblatt profile -/

/-- The normalizing constant of the full-space Barenblatt profile (eq. (Bxc)):
`c = (π^{d/2} Γ(p - d/2) / (b^{d/2} Γ(p)))^{2/(2p-d)}`. -/
noncomputable def fullBarenblattConst (d : ℕ) (p b : ℝ) : ℝ :=
  (π ^ ((d : ℝ) / 2) * Gamma (p - d / 2) / (b ^ ((d : ℝ) / 2) * Gamma p)) ^ (2 / (2 * p - d))

/-- The full-space Barenblatt profile with shape `p` and scale `b` (eq. (Bxc)):
`B(x) = (c + b|x|²)^{-p}` with `c = fullBarenblattConst d p b`. -/
noncomputable def fullBarenblatt (d : ℕ) (p b : ℝ) (x : E d) : ℝ :=
  (fullBarenblattConst d p b + b * ‖x‖ ^ 2) ^ (-p)

/-- **Lemma 3.1, eq. (Bac).** For `d ≥ 1`, `p > d/2`, `b > 0` and `-d < a < 2p - d`:
`∫ |x|ᵃ B(x) dx = (π^{d/2} Γ(p-d/2) / (bᵖ Γ(p)))^{a/(2p-d)} Γ((d+a)/2) Γ(p-(d+a)/2) /
(Γ(d/2) Γ(p-d/2))`. For `a = 0` this says that `B` is a probability density. -/
theorem fullBarenblatt_moment {d : ℕ} (hd : 1 ≤ d) {p b a : ℝ} (hp : (d : ℝ) / 2 < p)
    (hb : 0 < b) (ha0 : -(d : ℝ) < a) (ha : a < 2 * p - d) :
    ∫ x, ‖x‖ ^ a * fullBarenblatt d p b x =
      (π ^ ((d : ℝ) / 2) * Gamma (p - d / 2) / (b ^ p * Gamma p)) ^ (a / (2 * p - d)) *
        (Gamma ((d + a) / 2) * Gamma (p - (d + a) / 2) / (Gamma (d / 2) * Gamma (p - d / 2))) := by
  sorry

/-- **Lemma 3.1, eq. (Bm).** For `d ≥ 1`, `m > 0`, `b > 0` and `p > d/(2m)`, `p > d/2`:
`∫ B(x)ᵐ dx = (π/b)^{dp(1-m)/(2p-d)} (Γ(p)/Γ(p-d/2))^{(2pm-d)/(2p-d)} Γ(pm-d/2) / Γ(pm)`. -/
theorem fullBarenblatt_integral_rpow {d : ℕ} (hd : 1 ≤ d) {p b m : ℝ} (hm : 0 < m)
    (hp : (d : ℝ) / 2 < p) (hpm : (d : ℝ) / (2 * m) < p) (hb : 0 < b) :
    ∫ x, fullBarenblatt d p b x ^ m =
      (π / b) ^ (d * p * (1 - m) / (2 * p - d)) *
        (Gamma p / Gamma (p - d / 2)) ^ ((2 * p * m - d) / (2 * p - d)) *
        (Gamma (p * m - d / 2) / Gamma (p * m)) := by
  sorry

/-- **Lemma 3.1, eqs. (M2sim) and (difference-fde).** Fix `α > 1/2` and set
`m = ((d-2)α+1)/(dα)`, `p = 1/(1-m) = dα/(2α-1)`, `b = (2α-1)/(2(α(d-2)+1))`. Then as `d → ∞`,
`∫ |x|² B = (2πe)^{2α-1} d + o(d)`, `∫ Bᵐ = (2πe)^{2α-1} + o(1)`, and
`∫ |x|² B - d ∫ Bᵐ = O(1)`. -/
theorem fullBarenblatt_asymptotics {α : ℝ} (hα : 1 / 2 < α) :
    Tendsto (fun d : ℕ => (∫ x, ‖x‖ ^ 2 * fullBarenblatt d (d * α / (2 * α - 1))
        ((2 * α - 1) / (2 * (α * (d - 2) + 1))) x) / d) atTop
      (𝓝 ((2 * π * exp 1) ^ (2 * α - 1))) ∧
    Tendsto (fun d : ℕ => ∫ x, fullBarenblatt d (d * α / (2 * α - 1))
        ((2 * α - 1) / (2 * (α * (d - 2) + 1))) x ^ exponentOfAlpha α d) atTop
      (𝓝 ((2 * π * exp 1) ^ (2 * α - 1))) ∧
    (fun d : ℕ => (∫ x, ‖x‖ ^ 2 * fullBarenblatt d (d * α / (2 * α - 1))
        ((2 * α - 1) / (2 * (α * (d - 2) + 1))) x) -
      d * ∫ x, fullBarenblatt d (d * α / (2 * α - 1))
        ((2 * α - 1) / (2 * (α * (d - 2) + 1))) x ^ exponentOfAlpha α d) =O[atTop]
      (fun _ => (1 : ℝ)) := by
  sorry

/-! ## Lemmas 4.1 and 4.2: compactly supported Barenblatt profile -/

/-- The normalizing constant of the compactly supported Barenblatt profile (eq. (CBxc)):
`c = (b^{d/2} Γ(p+1+d/2) / (π^{d/2} Γ(p+1)))^{2/(2p+d)}`. -/
noncomputable def compactBarenblattConst (d : ℕ) (p b : ℝ) : ℝ :=
  (b ^ ((d : ℝ) / 2) * Gamma (p + 1 + d / 2) / (π ^ ((d : ℝ) / 2) * Gamma (p + 1))) ^
    (2 / (2 * p + d))

/-- The compactly supported Barenblatt profile with shape `p` and scale `b` (eq. (CBxc)):
`B(x) = (c - b|x|²)₊ᵖ` with `c = compactBarenblattConst d p b`. -/
noncomputable def compactBarenblatt (d : ℕ) (p b : ℝ) (x : E d) : ℝ :=
  (max (compactBarenblattConst d p b - b * ‖x‖ ^ 2) 0) ^ p

/-- **Lemma 4.1, eq. (CBac).** For `d ≥ 1`, `p > 0`, `b > 0` and `a > -d` (in particular all
`a ≥ 0`): `∫ |x|ᵃ B(x) dx = (Γ(p+1+d/2) / (π^{d/2} bᵖ Γ(p+1)))^{a/(d+2p)}
Γ(p+1+d/2) Γ((d+a)/2) / (Γ(d/2) Γ(p+1+(d+a)/2))`. For `a = 0`, `B` is a probability density. -/
theorem compactBarenblatt_moment {d : ℕ} (hd : 1 ≤ d) {p b a : ℝ} (hp : 0 < p) (hb : 0 < b)
    (ha : -(d : ℝ) < a) :
    ∫ x, ‖x‖ ^ a * compactBarenblatt d p b x =
      (Gamma (p + 1 + d / 2) / (π ^ ((d : ℝ) / 2) * b ^ p * Gamma (p + 1))) ^ (a / (d + 2 * p)) *
        (Gamma (p + 1 + d / 2) * Gamma ((d + a) / 2) /
          (Gamma (d / 2) * Gamma (p + 1 + (d + a) / 2))) := by
  sorry

/-- **Lemma 4.1, eq. (Bmpme).** For `d ≥ 1`, `p > 0`, `b > 0` and `m > 0`:
`∫ B(x)ᵐ dx = Γ(p+1+d/2)/Γ(pm+1+d/2) · Γ(pm+1)/Γ(p+1) ·
(b^{d/2}/π^{d/2} · Γ(p+1+d/2)/Γ(p+1))^{2p(m-1)/(2p+d)}`. -/
theorem compactBarenblatt_integral_rpow {d : ℕ} (hd : 1 ≤ d) {p b m : ℝ} (hp : 0 < p)
    (hb : 0 < b) (hm : 0 < m) :
    ∫ x, compactBarenblatt d p b x ^ m =
      Gamma (p + 1 + d / 2) / Gamma (p * m + 1 + d / 2) * (Gamma (p * m + 1) / Gamma (p + 1)) *
        (b ^ ((d : ℝ) / 2) / π ^ ((d : ℝ) / 2) * (Gamma (p + 1 + d / 2) / Gamma (p + 1))) ^
          (2 * p * (m - 1) / (2 * p + d)) := by
  sorry

/-- **Lemma 4.1, eqs. (limit-alpha-constant-pme) and (difference-pme).** Fix `α ∈ (0,1/2)` and
set `m = 1 + (1-2α)/(dα)` (that is, `m = exponentOfAlpha α d`), `p = 1/(m-1)`, `b = (m-1)/(2m)`.
Then as `d → ∞`, `∫ |x|² B = d/(2πe)^{1-2α} + o(d)`, `∫ Bᵐ = 1/(2πe)^{1-2α} + o(1)`, and
`∫ |x|² B - d ∫ Bᵐ = O(1)`. -/
theorem compactBarenblatt_asymptotics {α : ℝ} (hα0 : 0 < α) (hα : α < 1 / 2) :
    Tendsto (fun d : ℕ => (∫ x, ‖x‖ ^ 2 * compactBarenblatt d (1 / (exponentOfAlpha α d - 1))
        ((exponentOfAlpha α d - 1) / (2 * exponentOfAlpha α d)) x) / d) atTop
      (𝓝 (1 / (2 * π * exp 1) ^ (1 - 2 * α))) ∧
    Tendsto (fun d : ℕ => ∫ x, compactBarenblatt d (1 / (exponentOfAlpha α d - 1))
        ((exponentOfAlpha α d - 1) / (2 * exponentOfAlpha α d)) x ^ exponentOfAlpha α d) atTop
      (𝓝 (1 / (2 * π * exp 1) ^ (1 - 2 * α))) ∧
    (fun d : ℕ => (∫ x, ‖x‖ ^ 2 * compactBarenblatt d (1 / (exponentOfAlpha α d - 1))
        ((exponentOfAlpha α d - 1) / (2 * exponentOfAlpha α d)) x) -
      d * ∫ x, compactBarenblatt d (1 / (exponentOfAlpha α d - 1))
        ((exponentOfAlpha α d - 1) / (2 * exponentOfAlpha α d)) x ^ exponentOfAlpha α d)
      =O[atTop] (fun _ => (1 : ℝ)) := by
  sorry

/-- **Lemma 4.2.** Fix `m > 1` and set `p = 1/(m-1)`, `b = (m-1)/(2m)`. Then as `d → ∞`,
`c ~ bd/(2πe)`, `∫ |x|² B ~ d/(2πe)` and `∫ Bᵐ ~ 1/(2πe)`. -/
theorem compactBarenblatt_fixedExponent_asymptotics {m : ℝ} (hm : 1 < m) :
    Asymptotics.IsEquivalent atTop (fun d : ℕ => compactBarenblattConst d (1 / (m - 1))
        ((m - 1) / (2 * m))) (fun d => (m - 1) / (2 * m) * d / (2 * π * exp 1)) ∧
    Asymptotics.IsEquivalent atTop (fun d : ℕ => ∫ x, ‖x‖ ^ 2 * compactBarenblatt d (1 / (m - 1))
        ((m - 1) / (2 * m)) x) (fun d => d / (2 * π * exp 1)) ∧
    Asymptotics.IsEquivalent atTop (fun d : ℕ => ∫ x, compactBarenblatt d (1 / (m - 1))
        ((m - 1) / (2 * m)) x ^ m) (fun _ => 1 / (2 * π * exp 1)) := by
  sorry

/-- **After Lemma 4.2.** The compactly supported Barenblatt profile is positive exactly on the
open ball of radius `√(c/b)`, and for fixed `m > 1` (`p = 1/(m-1)`, `b = (m-1)/(2m)`) this
radius is equivalent to `√(d/(2πe))` as `d → ∞`. -/
theorem compactBarenblatt_support {m : ℝ} (hm : 1 < m) :
    (∀ (d : ℕ) {p b : ℝ}, 0 < p → 0 < b → ∀ x : E d,
      0 < compactBarenblatt d p b x ↔ ‖x‖ < √(compactBarenblattConst d p b / b)) ∧
    Asymptotics.IsEquivalent atTop
      (fun d : ℕ => √(compactBarenblattConst d (1 / (m - 1)) ((m - 1) / (2 * m)) /
        ((m - 1) / (2 * m))))
      (fun d => √(d / (2 * π * exp 1))) := by
  sorry

/-! ## Remark 3.2: full-space Barenblatt profiles and multivariate Student t-distributions -/

/-- The density of the multivariate Student t-distribution with position `x₀`, `r > 0` degrees of
freedom and (positive definite) scale matrix `Σ`:
`x ↦ C (1 + (x-x₀)ᵀΣ⁻¹(x-x₀)/r)^{-(r+d)/2}` with `C = Γ((r+d)/2) / (Γ(r/2) √det(rπΣ))`. -/
noncomputable def studentDensity (d : ℕ) (r : ℝ) (x₀ : E d) (S : Matrix (Fin d) (Fin d) ℝ)
    (x : E d) : ℝ :=
  Gamma ((r + d) / 2) / (Gamma (r / 2) * √(((r * π) • S).det)) *
    (1 + ⟪x - x₀, Matrix.toEuclideanCLM (𝕜 := ℝ) S⁻¹ (x - x₀)⟫_ℝ / r) ^ (-((r + d) / 2))

/-- The density of the Fisher–Snedecor F-distribution with `(d₁, d₂)` degrees of freedom:
`x ↦ (d₁/d₂)^{d₁/2} x^{d₁/2-1} (1 + d₁x/d₂)^{-(d₁+d₂)/2} / B(d₁/2, d₂/2)` on `(0,∞)`. -/
noncomputable def fisherSnedecorDensity (d₁ d₂ x : ℝ) : ℝ :=
  if 0 < x then
    (d₁ / d₂) ^ (d₁ / 2) * x ^ (d₁ / 2 - 1) * (1 + d₁ / d₂ * x) ^ (-((d₁ + d₂) / 2)) /
      (Gamma (d₁ / 2) * Gamma (d₂ / 2) / Gamma ((d₁ + d₂) / 2))
  else 0

/-- **Remark 3.2.** The law of `X = x₀ + Y/√(Z/r)`, with `Y ∼ 𝒩(0,Σ)` and `Z ∼ χ²(r) =
Gamma(r/2, 1/2)` independent, is the multivariate Student t-distribution. -/
theorem student_law {d : ℕ} (hd : 1 ≤ d) {r : ℝ} (hr : 0 < r) (x₀ : E d)
    {S : Matrix (Fin d) (Fin d) ℝ} (hS : S.PosDef) :
    ((ProbabilityTheory.multivariateGaussian 0 S).prod
        (ProbabilityTheory.gammaMeasure (r / 2) (1 / 2))).map
        (fun p => x₀ + (√(p.2 / r))⁻¹ • p.1) =
      densityMeasure (studentDensity d r x₀ S) := by
  sorry

/-- **Remark 3.2.** The Student t-distribution has a mean iff `r > 1`, equal to `x₀`, and a
covariance iff `r > 2`, equal to `r/(r-2) Σ`. -/
theorem student_moments {d : ℕ} (hd : 1 ≤ d) {r : ℝ} (hr : 0 < r) (x₀ : E d)
    {S : Matrix (Fin d) (Fin d) ℝ} (hS : S.PosDef) :
    (Integrable (fun x => ‖x‖ * studentDensity d r x₀ S x) ↔ 1 < r) ∧
    (1 < r → ∫ x, studentDensity d r x₀ S x • x = x₀) ∧
    (Integrable (fun x => ‖x‖ ^ 2 * studentDensity d r x₀ S x) ↔ 2 < r) ∧
    (2 < r → ∀ u v : E d, ∫ x, studentDensity d r x₀ S x * (⟪x - x₀, u⟫_ℝ * ⟪x - x₀, v⟫_ℝ) =
      r / (r - 2) * ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) S v⟫_ℝ) := by
  sorry

/-- **Remark 3.2.** At fixed `d`, the Student t-distribution tends to `𝒩(x₀, Σ)` as `r → ∞`
(weak convergence: integrals of bounded continuous functions converge). -/
theorem tendsto_student_gaussian {d : ℕ} (hd : 1 ≤ d) (x₀ : E d)
    {S : Matrix (Fin d) (Fin d) ℝ} (hS : S.PosDef) (φ : E d →ᵇ ℝ) :
    Tendsto (fun r => ∫ x, φ x * studentDensity d r x₀ S x) atTop
      (𝓝 (∫ x, φ x ∂(ProbabilityTheory.multivariateGaussian x₀ S))) := by
  sorry

/-- **Remark 3.2.** If `X` follows the Student t-distribution, then `(X-x₀)ᵀΣ⁻¹(X-x₀)/d` follows
the Fisher–Snedecor distribution `F(d, r)` (in the isotropic case `Σ = I`: `|X-x₀|²/d`); the law
of the Student t-distribution with `Σ = σ²I` is rotationally invariant around `x₀`. -/
theorem student_fisherSnedecor {d : ℕ} (hd : 1 ≤ d) {r : ℝ} (hr : 0 < r) (x₀ : E d)
    {S : Matrix (Fin d) (Fin d) ℝ} (hS : S.PosDef) :
    (densityMeasure (studentDensity d r x₀ S)).map
        (fun x => ⟪x - x₀, Matrix.toEuclideanCLM (𝕜 := ℝ) S⁻¹ (x - x₀)⟫_ℝ / d) =
      volume.withDensity (fun y => ENNReal.ofReal (fisherSnedecorDensity d r y)) ∧
    ∀ σ2 : ℝ, 0 < σ2 → ∀ U : E d ≃ₗᵢ[ℝ] E d, ∀ x,
      studentDensity d r x₀ (σ2 • 1) (x₀ + U (x - x₀)) = studentDensity d r x₀ (σ2 • 1) x := by
  sorry

/-- **Remark 3.2.** In the fast diffusion case, the Barenblatt profile and the equilibrium are
isotropic Student t-densities with `r = 1/(α(1-m))` degrees of freedom. -/
theorem barenblatt_eq_student {d : ℕ} {m : ℝ} (hd : 1 ≤ d) (hm0 : 0 < m) (hm1 : m < 1)
    (hmd : ((d : ℝ) - 2) / d < m) :
    (∃ σ2 : ℝ, 0 < σ2 ∧ ∀ x, barenblatt d m x =
      studentDensity d (1 / (alpha d m * (1 - m))) 0 (σ2 • 1) x) ∧
    ∃ σ2 : ℝ, 0 < σ2 ∧ ∀ x, equilibrium d m x =
      studentDensity d (1 / (alpha d m * (1 - m))) 0 (σ2 • 1) x := by
  sorry

/-- **Remark 3.2.** For `m = (d-1)/d` (`α = 1`), `B = v_∞` is the isotropic Student
t-density with `r = d` degrees of freedom and scale `σ_d² I`, where `σ_d² → 2πe`. -/
theorem barenblatt_student_dMinusOne :
    ∃ σ2 : ℕ → ℝ, (∀ᶠ d : ℕ in atTop, 0 < σ2 d ∧ ∀ x : E d,
        barenblatt d ((d - 1) / d) x = studentDensity d d 0 (σ2 d • 1) x ∧
        equilibrium d ((d - 1) / d) x = studentDensity d d 0 (σ2 d • 1) x) ∧
      Tendsto σ2 atTop (𝓝 (2 * π * exp 1)) := by
  sorry

/-! ## Remark 4.3: compactly supported Barenblatt profiles and projected spherical laws -/

/-- The uniform probability distribution on the centered sphere of radius `R` of `ℝᵈ`: the
normalized surface measure (Mathlib's `Measure.toSphere` of the Lebesgue measure, pushed
forward by `x ↦ R x`). -/
noncomputable def sphereUniform (d : ℕ) (R : ℝ) : Measure (E d) :=
  ((volume : Measure (E d)).toSphere Set.univ)⁻¹ •
    (volume : Measure (E d)).toSphere.map (fun x : sphere (0 : E d) 1 => R • (x : E d))

/-- The projection `(x₁, …, x_d) ↦ (x₁, …, x_n)` of `ℝᵈ` onto its first `n` coordinates. -/
noncomputable def projFirst {n d : ℕ} (h : n ≤ d) (x : E d) : E n :=
  WithLp.toLp 2 (fun i => x (Fin.castLE h i))

/-- **Remark 4.3.** If `X` is uniform on the sphere of radius `R` of `ℝᵈ`, then for
`1 ≤ n ≤ d-1`, `(X₁, …, X_n)` has density `C (R² - |y|²)^{(d-n-2)/2} 1_{|y| < R}` on `ℝⁿ`, with
`C = Γ(d/2) / (π^{n/2} Γ((d-n)/2) R^{d-2})`. -/
theorem sphereUniform_map_projFirst {n d : ℕ} (hn : 1 ≤ n) (hnd : n + 1 ≤ d) {R : ℝ}
    (hR : 0 < R) :
    (sphereUniform d R).map (projFirst (Nat.le_of_succ_le hnd)) =
      densityMeasure (fun y : E n => (ball (0 : E n) R).indicator (fun y =>
        Gamma (d / 2) / (π ^ ((n : ℝ) / 2) * Gamma ((d - n) / 2) * R ^ ((d : ℝ) - 2)) *
          (R ^ 2 - ‖y‖ ^ 2) ^ (((d : ℝ) - n - 2) / 2)) y) := by
  sorry

/-- **Remark 4.3.** If `Z ∼ 𝒩(0, I_d)` then `R Z/|Z|` is uniform on the sphere of radius `R`. -/
theorem stdGaussian_map_sphereUniform {d : ℕ} (hd : 1 ≤ d) (R : ℝ) :
    (ProbabilityTheory.stdGaussian (E d)).map (fun z => (R / ‖z‖) • z) = sphereUniform d R := by
  sorry

/-- The stereographic projection `x ↦ (x₁, …, x_{d-1}) / (1 - x_d)` from the unit sphere of `ℝᵈ`
(minus its north pole) onto `ℝ^{d-1}`. -/
noncomputable def stereoProj {d : ℕ} (hd : 1 ≤ d) (x : E d) : E (d - 1) :=
  (1 - x ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩)⁻¹ • projFirst (Nat.sub_le d 1) x

/-- **Remark 4.3, stereographic projection.** If `X` is uniform on the unit sphere of `ℝᵈ`,
`d ≥ 2`, then its stereographic projection on `ℝ^{d-1}` has the full-space Barenblatt density
`Γ(d-1) / (π^{(d-1)/2} Γ((d-1)/2)) (1 + |y|²)^{-(d-1)}` (no extra radial weight). -/
theorem sphereUniform_map_stereoProj {d : ℕ} (hd : 2 ≤ d) :
    (sphereUniform d 1).map (stereoProj (Nat.le_of_succ_le hd)) =
      densityMeasure (fun y : E (d - 1) => Gamma ((d : ℝ) - 1) /
        (π ^ (((d : ℝ) - 1) / 2) * Gamma (((d : ℝ) - 1) / 2)) * (1 + ‖y‖ ^ 2) ^ (-((d : ℝ) - 1))) := by
  sorry

end Cutfast
