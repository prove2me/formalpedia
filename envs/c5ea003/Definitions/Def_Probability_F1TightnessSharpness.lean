-- Prove2me | Definitions.Def_Probability_F1TightnessSharpness
-- name    : Probability_F1TightnessSharpness
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:14:19.020924+00:00
-- url     : https://prove2.me/theorems/c42461e0-1210-4df3-8e0d-e3ac1c60a661
-- title:
--   Aether Catalog definitions — Probability_F1TightnessSharpness
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.F1TightnessSharpness`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/F1TightnessSharpness.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Probability_F1TightnessCore

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

namespace F1Tightness

/-! ## A two-cell family approaching flatness -/

/-- The two-cell profile `(1/2 + δ, 1/2 − δ)`. -/
noncomputable def twoCell (δ : ℝ) : Fin 2 → ℝ := fun i => if i = 0 then 1 / 2 + δ else 1 / 2 - δ










/-! ## Stability of the slack factor ("hump-insensitivity") -/

variable {M : ℕ}



/-! ## A worked rational example -/


/-! ## Which arm of the master bound binds -/

/-- The two-armed master bound `min(1/(ΛΘq̂), 2^k/(ΛΘ))`. -/
noncomputable def boundF1two (lam th q : ℝ) (k : ℕ) : ℝ :=
  min (1 / (lam * th * q)) ((2 : ℝ) ^ k / (lam * th))



end F1Tightness


