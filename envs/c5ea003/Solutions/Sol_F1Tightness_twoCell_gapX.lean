-- Prove2me | solution 1 for F1Tightness.twoCell_gapX
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:48:29.737686+00:00
-- url     : https://prove2.me/submissions/be2e4f65-a78d-4e63-ac02-e5ccc8bad05d

-- Sol generated from Probability/F1TightnessSharpness.lean
import Mathlib
import Definitions.Def_Probability_F1TightnessCore
import Definitions.Def_Probability_F1TightnessSharpness
import Theorems.Thm_F1Tightness_twoCell_scanCost

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
theorem solution(δ : ℝ) :
    gapX (twoCell δ) = (3 / 2) / (3 / 2 - δ) := by
  rw [gapX, twoCell_scanCost, baseCost]
  norm_num
