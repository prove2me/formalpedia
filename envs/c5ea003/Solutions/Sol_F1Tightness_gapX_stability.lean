-- Prove2me | solution 1 for F1Tightness.gapX_stability
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:58:03.023418+00:00
-- url     : https://prove2.me/submissions/3d4bb840-3443-4e73-a581-7a00704117e4

-- Sol generated from Probability/F1TightnessSharpness.lean
import Mathlib
import Definitions.Def_Probability_F1TightnessCore
import Definitions.Def_Probability_F1TightnessSharpness
import Theorems.Thm_F1Tightness_baseCost_pos
import Theorems.Thm_F1Tightness_one_le_scanCost
import Theorems.Thm_F1Tightness_scanCost_sub_abs_le

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
theorem solution{p q : Fin M → ℝ} (hp : ∀ i, 0 ≤ p i)
    (hsump : ∑ i : Fin M, p i = 1) (hq : ∀ i, 0 ≤ q i) (hsumq : ∑ i : Fin M, q i = 1) :
    |gapX p - gapX q| ≤ ((M : ℝ) + 1) / 2 * ((M : ℝ) * ∑ i : Fin M, |p i - q i|) := by
  have hcp : 1 ≤ scanCost p := one_le_scanCost hp hsump
  have hcq : 1 ≤ scanCost q := one_le_scanCost hq hsumq
  have hcp0 : 0 < scanCost p := by linarith
  have hcq0 : 0 < scanCost q := by linarith
  have hb : 0 < baseCost M := baseCost_pos M
  have hdiff : gapX p - gapX q
      = baseCost M * (scanCost q - scanCost p) / (scanCost p * scanCost q) := by
    unfold gapX
    field_simp
  rw [hdiff, abs_div, abs_mul, abs_of_pos (by positivity : (0:ℝ) < scanCost p * scanCost q),
    abs_of_pos hb]
  rw [div_le_iff₀ (by positivity)]
  have habs : |scanCost q - scanCost p| ≤ (M : ℝ) * ∑ i : Fin M, |p i - q i| := by
    have := scanCost_sub_abs_le q p
    have hsymm : ∑ i : Fin M, |q i - p i| = ∑ i : Fin M, |p i - q i| :=
      Finset.sum_congr rfl fun i _ => abs_sub_comm _ _
    rwa [hsymm] at this
  have hsum0 : 0 ≤ (M : ℝ) * ∑ i : Fin M, |p i - q i| := by
    have : 0 ≤ ∑ i : Fin M, |p i - q i| := Finset.sum_nonneg fun i _ => abs_nonneg _
    positivity
  have hprod : 1 ≤ scanCost p * scanCost q := by nlinarith
  have hbc : baseCost M = ((M : ℝ) + 1) / 2 := rfl
  calc baseCost M * |scanCost q - scanCost p|
      ≤ baseCost M * ((M : ℝ) * ∑ i : Fin M, |p i - q i|) :=
        mul_le_mul_of_nonneg_left habs hb.le
    _ ≤ ((M : ℝ) + 1) / 2 * ((M : ℝ) * ∑ i : Fin M, |p i - q i|) *
          (scanCost p * scanCost q) := by
        rw [hbc]
        have hK : 0 ≤ ((M : ℝ) + 1) / 2 * ((M : ℝ) * ∑ i : Fin M, |p i - q i|) := by
          have : (0:ℝ) ≤ ((M : ℝ) + 1) / 2 := by positivity
          exact mul_nonneg this hsum0
        exact le_mul_of_one_le_right hK hprod
