-- Prove2me | solution 1 for F1Tightness.scanCost_sub_abs_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:54:12.256747+00:00
-- url     : https://prove2.me/submissions/b031ead3-4ded-42f3-b339-1d59c0918e80

-- Sol generated from Probability/F1TightnessSharpness.lean
import Mathlib
import Definitions.Def_Probability_F1TightnessCore
import Definitions.Def_Probability_F1TightnessSharpness

/-!
# Sharpness over the prior class, stability, and the binding arm (paper 250)

`Probability.F1TightnessCore` proves that on a fixed front-loaded, non-flat
positional profile the F1 master bound is *never attained*: the slack factor
`X = C₀/c_asc` is strictly larger than one.  The natural objection is that the
inequality might then be improvable.  This file shows it is not: the bound is
**sharp over the prior class** even though it is unattainable on any fixed
non-flat pool.  This is the theorem-side closer named in the round-92
deliverable: sharpness must be posed over the class of priors, never as
tightness on one pool.

Main results.

* `twoCell` — the two-cell family `p_δ = (1/2 + δ, 1/2 − δ)`, antitone and
  non-flat for `0 < δ < 1/2`, with slack factor `X = (3/2)/(3/2 − δ)`.
* `twoCell_gapX`, `twoCell_slack_small` — the slack of `p_δ` tends to `1`.
* `sharp_over_prior_class` — for every `ε > 0` there is an admissible
  (antitone, non-flat) profile whose slack is `< 1 + ε`: the constant `1`
  cannot be improved uniformly over the prior class, yet
  `slack_never_attained` says no admissible profile reaches it.
* `gapX_stability` — the slack factor is Lipschitz in the profile for the `L¹`
  distance; this is the formal content of "hump-insensitivity": a bounded
  perturbation of the profile moves `X` by a bounded amount.
* `binding_arm` — with `k_bits = 0` and `q̂ ≥ 1` the first arm of the master
  bound `min(1/(ΛΘq̂), 2^k/(ΛΘ))` is the binding one, as booked.
-/

open Finset

open F1Tightness

/-! ## A two-cell family approaching flatness -/











/-! ## Stability of the slack factor ("hump-insensitivity") -/

variable {M : ℕ}



/-! ## A worked rational example -/


/-! ## Which arm of the master bound binds -/





open F1Tightness in
theorem solution(p q : Fin M → ℝ) :
    |scanCost p - scanCost q| ≤ (M : ℝ) * ∑ i : Fin M, |p i - q i| := by
  have hdiff : scanCost p - scanCost q
      = ∑ i : Fin M, (((i : ℕ) : ℝ) + 1) * (p i - q i) := by
    rw [scanCost, scanCost, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hdiff]
  calc |∑ i : Fin M, (((i : ℕ) : ℝ) + 1) * (p i - q i)|
      ≤ ∑ i : Fin M, |(((i : ℕ) : ℝ) + 1) * (p i - q i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin M, (M : ℝ) * |p i - q i| := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_mul]
        have h1 : |((i : ℕ) : ℝ) + 1| ≤ (M : ℝ) := by
          have hb : ((i : ℕ) : ℝ) + 1 ≤ (M : ℝ) := by exact_mod_cast i.isLt
          rw [abs_of_nonneg (by positivity)]
          exact hb
        exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
    _ = (M : ℝ) * ∑ i : Fin M, |p i - q i| := by rw [Finset.mul_sum]
