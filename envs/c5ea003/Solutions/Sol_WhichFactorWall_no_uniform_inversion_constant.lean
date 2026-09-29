-- Prove2me | solution 1 for WhichFactorWall.no_uniform_inversion_constant
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T15:11:05.672504+00:00
-- url     : https://prove2.me/submissions/227108d1-1333-4f1f-a982-e4d421897996

-- Sol generated from Algebra/WhichFactorWallInvariant.lean
import Mathlib
import Definitions.Def_Algebra_WhichFactorWallInvariant
import Theorems.Thm_WhichFactorWall_log_two_sub_binEntropy_le_sq
/-
# The which-factor wall as a cross-population invariant: how much does it really pin down?

This file continues `Speculative.AutoResearch.TraceBatteryWall`
(`TraceBattery.binary_wall_inversion`), which shows that a *binary* capacity
("wall") value determines the class imbalance of a two-valued statistic
**uniquely** on the balanced side `[0, 1/2]`.  Uniqueness, however, is a
qualitative statement.  The research question of this cycle is quantitative:

> if two independent populations report walls that agree to within `ε`,
> how close are their class imbalances?

The mission proposal was:

  `|binEntropy p - binEntropy q| ≥ c(δ) |p - q|` on `[δ, 1/2]`,
  with `c(δ) = log ((1-δ)/δ)`.

**This is false**, and `binEntropy_conjectured_lower_bound_false` refutes it with
an exact counterexample (`δ = q = 1/4`, `p = 1/2`), where the failure reduces to
`log 16 ≤ log 27`.  The reason is structural: `c(δ)` is the *supremum* of
`|binEntropy'|` on `[δ, 1/2]`, not its infimum, so it controls the Lipschitz
(upper) bound, while the true inverse bound must be governed by the derivative
at the endpoint *closest to* `1/2`.

What survives, and is proved here with zero sorries:

* `binEntropy_sub_ge` — the sharp mean-value lower bound
  `(q - p) * (log (1-q) - log q) ≤ binEntropy q - binEntropy p` for
  `0 ≤ p ≤ q ≤ 1/2` (including the boundary case `p = 0`).
* `binEntropy_lipschitz` — the true version of the proposed inequality, with the
  inequality reversed: `|binEntropy p - binEntropy q| ≤ c(δ) |p - q|` on
  `[δ, 1-δ]`.
* `imbalance_dist_le` / `imbalance_dist_le_div` — the corrected **cross-population
  stability theorem**: imbalances in `[0, 1/2 - η]` whose walls agree within `ε`
  agree within `ε / log ((1/2+η)/(1/2-η))`.
* `binary_wall_stability` — the same statement at the level of two binary
  statistics on two different finite populations, via the empirical entropy `H`.
* `log_two_sub_binEntropy_le_sq` — `log 2 - binEntropy (1/2 - t) ≤ 4 t²`, and
  `no_uniform_inversion_constant`: **no** constant inverts the wall near `1/2`.
  So the guard `η > 0` is not an artefact: the wall genuinely loses all
  resolution at balance, at a quadratic rate.
* `wall_imbalance_bracket` — the reported wall `0.4677` bits is a falsifiable
  claim about the split: the unique minority fraction in `[0, 1/2]` realising it
  lies strictly between `1/12` and `1/9` (i.e. between 8.34% and 11.11%),
  consistent with the reported 9.96% and inconsistent with, say, a 5% or a 15%
  split.

Because the catalog module `Combinatorics.TraceBatteryEntropy` carrying the
empirical-entropy definitions is not present in this snapshot, the small
population layer (`img`, `cnt`, `H`, `H_two_values`) is restated here in the
open `WhichFactorWall`,
self-contained and compiles on its own.
-/

open WhichFactorWall

open Real Set

/-! ## 1.  Mean-value machinery for `Real.binEntropy`

`binEntropy` is differentiable away from `{0,1}` with derivative
`log (1-x) - log x` (Mathlib's `Real.deriv_binEntropy`).  We turn one-sided
bounds on that derivative into slope bounds by monotonicity of an auxiliary
function; this is the mean value theorem in the form we need. -/







/-! ## 2.  Refutation of the proposed inverse bound -/


/-! ## 3.  Corrected cross-population stability -/



/-! ## 4.  Why the guard `η > 0` cannot be dropped: quadratic degeneracy at balance -/



/-! ## 5.  Population layer: empirical entropy of a two-valued statistic

These are the definitions of the catalog's trace-battery entropy module,
restated so that this file is self-contained. -/


variable {Ω : Type*} [Fintype Ω] [Nonempty Ω] {α : Type*}




variable [DecidableEq α]






/-! ## 6.  The reported wall `0.4677` bits as a falsifiable claim about the split -/













theorem solution(C η : ℝ) (hη : 0 < η) :
    ∃ p q : ℝ, p ∈ Icc (2⁻¹ - η) (2⁻¹ : ℝ) ∧ q ∈ Icc (2⁻¹ - η) (2⁻¹ : ℝ) ∧ p ≠ q ∧
      C * |binEntropy p - binEntropy q| < |p - q| := by
  set t : ℝ := min (min η 4⁻¹) (1 / (8 * (|C| + 1))) with ht
  have hCpos : (0 : ℝ) < |C| + 1 := by positivity
  have ht0 : 0 < t := by
    rw [ht]
    exact lt_min (lt_min hη (by norm_num)) (by positivity)
  have htη : t ≤ η := le_trans (min_le_left _ _) (min_le_left _ _)
  have ht4 : t ≤ 4⁻¹ := le_trans (min_le_left _ _) (min_le_right _ _)
  have htC : t ≤ 1 / (8 * (|C| + 1)) := min_le_right _ _
  refine ⟨2⁻¹ - t, 2⁻¹, ⟨by linarith, by linarith⟩, ⟨by linarith, le_refl _⟩,
    by intro h; rw [sub_eq_self] at h; linarith, ?_⟩
  have hquad : log 2 - binEntropy (2⁻¹ - t) ≤ 4 * t ^ 2 :=
    log_two_sub_binEntropy_le_sq ht0.le (by linarith)
  have hle : binEntropy (2⁻¹ - t) ≤ log 2 := by
    simpa using (Real.binEntropy_le_log_two (p := 2⁻¹ - t))
  have habs1 : |binEntropy (2⁻¹ - t) - binEntropy 2⁻¹| = log 2 - binEntropy (2⁻¹ - t) := by
    rw [Real.binEntropy_two_inv, abs_of_nonpos (by linarith)]
    ring
  have habs2 : |(2⁻¹ - t : ℝ) - 2⁻¹| = t := by
    rw [show (2⁻¹ - t : ℝ) - 2⁻¹ = -t by ring, abs_neg, abs_of_nonneg ht0.le]
  rw [habs1, habs2]
  have hstep : C * (log 2 - binEntropy (2⁻¹ - t)) ≤ |C| * (4 * t ^ 2) := by
    have h0 : 0 ≤ log 2 - binEntropy (2⁻¹ - t) := by linarith
    nlinarith [hquad, le_abs_self C, abs_nonneg C]
  have hfinal : |C| * (4 * t ^ 2) < t := by
    have h2 : |C| * (4 * t) ≤ |C| * (4 * (1 / (8 * (|C| + 1)))) := by
      nlinarith [abs_nonneg C]
    have h3 : |C| * (4 * (1 / (8 * (|C| + 1)))) < 1 := by
      rw [show |C| * (4 * (1 / (8 * (|C| + 1)))) = |C| / (2 * (|C| + 1)) by field_simp; ring,
        div_lt_one (by positivity)]
      nlinarith [abs_nonneg C]
    nlinarith [ht0, h2, h3]
  linarith
