# Errata for arXiv v1 of the paper, found during the Lean formalization

Mathematical issues in *On the cutoff phenomenon for fast diffusion and porous medium
equations* (D. Chafaï, M. Fathi, N. Simonov), version 1 on arXiv
([arXiv:2503.11770v1](https://arxiv.org/abs/2503.11770v1)), found while formalizing it in Lean.
All the fixes below are applied to version 2
([arXiv:2503.11770v2](https://arxiv.org/abs/2503.11770v2)), and to `cutfast-lean.tex` in this
repository.

## Errors in arXiv v1 and their fixes

1. **Lemma 3.1, eq. (Bac), and eq. (Ba) in its proof: wrong range for `a`.**
   - Paper: "for all `a > d − 2p`".
   - Fix: `−d < a < 2p − d`.
   - Why: `∫|x|^a (c + b|x|²)^{−p} dx` converges at the origin iff `a > −d`, and at infinity iff
     `a − 2p < −d`. Correspondingly, `Γ((d+a)/2)` and `Γ(p − (d+a)/2)` must both have positive
     arguments.
   - Lean: `Cutfast.fullBarenblatt_moment`, hypotheses `ha0 : -d < a` and `ha : a < 2p - d`.

2. **Lemma 4.1, eq. (Bmpme): `m = 0` excluded.**
   - Paper: "for all `m ≥ 0`".
   - Fix: `m > 0`.
   - Why: for `m = 0` the formula gives the volume of the support ball, which is correct only
     with the convention `0⁰ = 0`. With the usual convention, `B⁰ ≡ 1` on all of `ℝᵈ` and the
     integral diverges.
   - Lean: `Cutfast.compactBarenblatt_integral_rpow`, hypothesis `hm : 0 < m`.

3. **Theorems 1.1 and 1.2: range of `ε`.**
   - Paper: "for all `ε > 0`".
   - Fix: `ε ∈ (0,1)`, and the same in the proof ("Let `ε ∈ (0,1)`").
   - Why: for `ε ≥ 1` the time `t_d = (1 − ε)·c·log d` in the `+∞` case is not positive, so
     `v(t_d, ·)` is not defined by (FDEFPv).
   - Lean: the `+∞` conjunct of every `Cutfast.cutoff_*` theorem has the hypothesis `ε < 1`.
     The `0` conjunct holds for every `ε > 0`.

4. **Lemma 2.2: positive definiteness needed.**
   - Paper: `Σ_μ`, `Σ_ν` positive semidefinite.
   - Fix: `Σ_μ` positive definite, `Σ_ν` positive semidefinite.
   - Why: the proof defines `A = √Σ_μ⁻¹ √(√Σ_μ Σ_ν √Σ_μ) √Σ_μ⁻¹`. In general (e.g. `Σ_μ = 0`
     with `ν` non-degenerate) no transport map exists.
   - Lean: `Cutfast.wassersteinSq_elliptic` assumes both `Σ_μ` and `Σ_ν` positive definite.
     This is stronger than the fixed paper, and avoids a polar decomposition for singular `Σ_ν`.

5. **Lemma 2.1, proof: wrong moment relation.**
   - Paper: "`Σ_μ = M_μ + m_μ m_μᵀ`".
   - Fix: `M_μ = Σ_μ + m_μ m_μᵀ`, since the covariance is the second moment minus `m_μ m_μᵀ`.

6. **Lemma 2.1, proof: wrong cross-reference.**
   - The proof said "To get (W2sig)". (W2sig) is the formula of Lemma 2.2.
   - Fix: the covariance formula of Lemma 2.1 now has its own label `eq:W2cov`, and the proof
     cites it.

7. **Proof of Theorem 1.1 (fast diffusion), eq. (inequality-hm): missing square.**
   - Paper: `|x₀| e^{−2t}/2`.
   - Fix: `|x₀|² e^{−2t}/2`.

## Errors in the remarks (also fixed in `cutfast-lean.tex`)

These were found while writing or auditing the corresponding statements in `Challenge.lean`;
their Lean proofs are in `Cutfast/Student.lean`, `Cutfast/Sphere.lean` and `Cutfast/Entropy.lean`.

8. **Remark 4.3: wrong normalizing constant of the projected spherical law.**
   - Paper: `C = 2 / (R^{d−2} Beta(n/2, (d−n)/2))`.
   - Fix: `C = Γ(d/2) / (π^{n/2} Γ((d−n)/2) R^{d−2})`. The paper's value is too large by the
     factor `|S^{n−1}| = 2π^{n/2}/Γ(n/2)`.
   - Check: for `d = 3`, `n = 1` (Archimedes), `X₁` is uniform on `[−R, R]` with density
     `1/(2R)`, while the paper's constant gives `1/R`, of total mass 2.
   - Lean: `Cutfast.sphereUniform_map_projFirst`.

9. **Remark 3.2: wrong normalization in the Fisher–Snedecor claim.**
   - Paper: "`(1/r)|X − x₀|²` follows a Fisher–Snedecor F-distribution".
   - Fix: `(X − x₀)ᵀ Σ⁻¹ (X − x₀)/d ∼ F(d, r)`; in the isotropic case `Σ = I`, `|X − x₀|²/d`.
     Indeed `|X − x₀|² = |Y|² r/Z`, so `(1/r)|X − x₀|² = |Y|²/Z = (d/r)·F(d, r)`.
   - Lean: `Cutfast.student_fisherSnedecor`.

10. **Remark 3.2: limit as `r → ∞`.**
    - Paper: the Student law tends to `𝒩(0, Σ)`.
    - Fix: `𝒩(x₀, Σ)`. The paper's limit is right only for `x₀ = 0`.
    - Lean: `Cutfast.tendsto_student_gaussian`.

11. **Remark 4.3: stereographic projection.**
    - Paper: the stereographic projection of the uniform law on the sphere gives "the
      deformation of a full space Barenblatt profile by a radial power weight".
    - Fix: for the uniform law on the unit sphere of `ℝᵈ`, the image law on `ℝ^{d−1}` has density
      `Γ(d−1)/(π^{(d−1)/2} Γ((d−1)/2)) · (1 + |y|²)^{−(d−1)}`. This is exactly a full-space
      Barenblatt (multivariate Student, `r = d − 1`) profile, with no extra radial weight.
    - Lean: `Cutfast.sphereUniform_map_stereoProj`.

12. **Remark 4.3: typo in the projection.**
    - Paper: `π_n(x₁, …, x_n) = (x₁, …, x_n)`.
    - Fix: `π_n(x₁, …, x_d) = (x₁, …, x_n)`.

13. **Section 1.3: the limit `m → 1` of the Tsallis function.**
    - Paper: "`x ↦ (xᵐ − 1)/(m − 1)` … gives the classical logarithmic relative entropy as `m → 1`".
    - Problem: `(xᵐ − 1)/(m − 1)` diverges as `m → 1` when `x ≠ 1`, since the numerator tends to
      `x − 1`.
    - Fix: subtract the affine term `(x − 1)/(m − 1)`, whose integral vanishes between probability
      densities. Then `(xᵐ − x)/(m − 1) → x log x`.
    - Found by the Lean agent: the first, literal statement was disproved, with counterexample
      `x = 2` (`Cutfast.Entropy.tsallis_not_tendsto`).
    - Lean: `Cutfast.tsallis_strictConvexOn_tendsto_log`.

14. **Remark 4.3: the projected spherical law is a Barenblatt profile only for `n ≤ d − 3`.**
    - Paper: "We recognize a compactly supported Barenblatt profile with shape parameter
      `p = (d−n−2)/2`", for all `1 ≤ n ≤ d − 1`.
    - Problem: Lemma 4.1 requires `p > 0`, that is `n ≤ d − 3`. For `n = d − 2`, `p = 0` and the
      law is uniform on the ball of radius `R`. For `n = d − 1`, `p = −1/2 < 0`: the density
      `C (R² − |y|²)^{−1/2}` blows up at the boundary (arcsine law for `d = 2`), and it is not a
      Barenblatt profile.
    - Fix: state the identification for `n ≤ d − 3`, and describe the cases `n = d − 2` and
      `n = d − 1` separately. The density formula itself is right for all `1 ≤ n ≤ d − 1` (with
      the indicator form, which avoids `0⁰` when `n = d − 2`).
    - Found when auditing the statements; `Challenge.lean` states only the density formula, so no
      Lean statement changes.
    - Lean: `Cutfast.sphereUniform_map_projFirst`.

## Improvements found, not applied to the paper

- **Eqs. (difference-fde) and (difference-pme) are exact identities.** With
  `b = (1−m)/(2m)` and `p = 1/(1−m)` (resp. `b = (m−1)/(2m)`, `p = 1/(m−1)`), one has
  `∫|x|² B = d ∫ Bᵐ` exactly, not merely up to `O(1)`.
  - Proof: `Bᵐ = B·(c ± b|x|²)` because `p(m−1) = ∓1`, so `∫Bᵐ = c ± b M₂`. The Gamma formula
    for `M₂` then gives `M₂(1 ∓ db) = dc`.
  - The same identity holds for `v_∞` (virial identity: `∇(v_∞ᵐ) = −x v_∞`). It gives exact
    closed forms along the flow, with `a = (1 − e^{−t/α})^α`, `h = e^{−t}x₀`, `κ = d(1−m)`:
    - `W₂² = (1−a)² M₂ + |h|²`;
    - `Hₘ = M₂ ((1−a^κ)/κ − (1−a²)/2) + |h|²/2`;
    - `Iₘ = a²(1 − a^{−1/α})² M₂ + |h|²`.
  - Lean: `Cutfast.fullBarenblatt_secondMoment_eq`, `Cutfast.compactBarenblatt_secondMoment_eq`,
    `Cutfast.integral_equilibrium_rpow`, and `Cutfast/Distances.lean`.

- **Theorems 1.1 and 1.2 need only weak information on `M₂`.** From the exact formulas above,
  the cutoff needs only `c·d ≤ M₂ ≤ C·d` for Theorem 1.1, and only `M₂ = O(d)` for Theorem 1.2.
  The precise `(2πe)` constants are not used.

- **Lemma 2.1 holds without Brenier's theorem.** There is an elementary proof by Fenchel–Young
  with the regularization `A + δI`, `δ → 0`, valid for every positive semidefinite `A`
  (`Cutfast/Wasserstein.lean`).

## Formalization choices (not errors)

Recorded under `fidelity` in `formalization.yaml`:

- `W₂²` and `Iₘ` take values in `[0, ∞]`.
- `Hₘ` is a Bochner integral, so its integrability is stated explicitly, and the supremum over
  `x₀` is taken in `EReal`.
- In Lemma 2.1, `Tr((A−I)² M_μ)` appears as `∫|(A−I)x|² dμ`.
- The solution `v` is the explicit formula (FDEFPv), as in the paper. Its PDE is proved
  separately (`Cutfast.solution_hasDerivAt`).
- Not formalized: uniqueness for the PDE with Dirac data, the qualitative comments of
  Sections 1.4.1, 1.4.4–1.4.6, and Demange's spherical profile (Section 1.4.5), which would need
  the Laplace–Beltrami operator (not in Mathlib) and whose normalization is not stated.
