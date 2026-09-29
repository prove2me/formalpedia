-- Prove2me | Theorems.Thm_F1Tightness_twoCell_gapX
-- name    : F1Tightness.twoCell_gapX
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:24:27.672537+00:00
-- url     : https://prove2.me/theorems/c5a93b5a-06ad-4eda-98e8-2708d9f34f2c
-- title:
--   The slack factor of the two-cell family.
-- statement:
--   The slack factor of the two-cell family.
--
--   ```lean
--   theorem F1Tightness.twoCell_gapX(δ : ℝ) :
--       gapX (twoCell δ) = (3 / 2) / (3 / 2 - δ) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/F1TightnessSharpness.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/F1TightnessSharpness.lean#L63

-- Thm stub generated from Probability/F1TightnessSharpness.lean
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

theorem F1Tightness.twoCell_gapX(δ : ℝ) :
    gapX (twoCell δ) = (3 / 2) / (3 / 2 - δ) := by sorry
