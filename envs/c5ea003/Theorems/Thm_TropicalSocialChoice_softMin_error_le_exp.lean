-- Prove2me | Theorems.Thm_TropicalSocialChoice_softMin_error_le_exp
-- name    : TropicalSocialChoice.softMin_error_le_exp
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:18:19.161928+00:00
-- url     : https://prove2.me/theorems/e35fd25b-db25-4468-af9b-92bda8b72e66
-- title:
--   The conjectured form of the error bound: for `t ≥ 1` the deviation of the Boltzmann
-- statement:
--   The conjectured form of the error bound: for `t ≥ 1` the deviation of the Boltzmann
--   aggregator from the pivotal-corrected tropical value is at most `C e^{−tΔ}` with
--   `C = #s`, a constant depending only on the size of the coalition.
--
--   ```lean
--   theorem TropicalSocialChoice.softMin_error_le_exp(s : Finset ι) (hs : s.Nonempty) (y : ι → ℝ) {t Δ : ℝ}
--       (ht : 1 ≤ t) (hgap : ∀ i ∈ s, i ∉ pivotal s hs y → s.inf' hs y + Δ ≤ y i) :
--       (s.inf' hs y - Real.log (pivotal s hs y).card / t) - softMin s t y
--         ≤ (s.card : ℝ) * Real.exp (-(t * Δ)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/TropicalSocialChoiceDequantisation.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/TropicalSocialChoiceDequantisation.lean#L151

-- Thm stub generated from Probability/TropicalSocialChoiceDequantisation.lean
import Mathlib
import Definitions.Def_Probability_TropicalSocialChoice
import Definitions.Def_Probability_TropicalSocialChoiceOligarchy
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.
-/

/-!
# Tropical social choice V: exponentially sharp Maslov dequantisation

`Probability.TropicalSocialChoice` proved the crude two-sided bound
`min y − log (#s)/t ≤ softMin s t y ≤ min y` for the Boltzmann aggregator
`softMin s t y = −(1/t) log ∑_{i ∈ s} exp (−t yᵢ)`, and
`Probability.TropicalSocialChoiceOligarchy` sharpened the upper bound to
`softMin s t y ≤ min y − log m / t`, where `m` is the number of *pivotal* (cost-minimising)
voters.

Conjecture 2 of `FUTURE_DIRECTIONS.md` asserted that `m`, not `#s`, controls **both** sides,
the remaining error being exponentially small in the gap `Δ` between the minimal cost and
the next one.  This file proves it.

## Main results

* `softMin_ge_of_gap` : if every non-pivotal member of the coalition has cost at least
  `min y + Δ`, then
  `min y − log m / t − (q/m)·e^{−tΔ}/t ≤ softMin s t y`, where `q = #(s \ pivotal)`.
* `softMin_sandwich_of_gap` : combining with the proved upper bound,
  `0 ≤ (min y − log m / t) − softMin s t y ≤ (q/m)·e^{−tΔ}/t`.
* `softMin_error_le_exp` : for `t ≥ 1` the error is at most `(#s)·e^{−tΔ}`, i.e. the
  conjectured form `C e^{−tΔ}` with `C` depending only on `#s`.
* `exists_gap` : the gap hypothesis is never vacuous — whenever some member of the
  coalition is not pivotal, a strictly positive `Δ` with that property exists.
* `softMin_eq_of_pivotal_eq_self` : when *all* members are pivotal the Boltzmann value is
  exactly `min y − log (#s)/t`, so the `log m / t` term of the upper bound cannot be
  improved.
* `softMin_tendsto_exp_error` : the rescaled error `e^{tΔ/2}·(error)` tends to `0`, the
  quantitative form of the zero-temperature limit.
-/

open TropicalSocialChoice

open Finset Filter


variable {ι : Type*} [DecidableEq ι]

theorem TropicalSocialChoice.softMin_error_le_exp(s : Finset ι) (hs : s.Nonempty) (y : ι → ℝ) {t Δ : ℝ}
    (ht : 1 ≤ t) (hgap : ∀ i ∈ s, i ∉ pivotal s hs y → s.inf' hs y + Δ ≤ y i) :
    (s.inf' hs y - Real.log (pivotal s hs y).card / t) - softMin s t y
      ≤ (s.card : ℝ) * Real.exp (-(t * Δ)) := by sorry
