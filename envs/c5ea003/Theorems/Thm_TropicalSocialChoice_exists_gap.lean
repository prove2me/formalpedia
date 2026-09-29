-- Prove2me | Theorems.Thm_TropicalSocialChoice_exists_gap
-- name    : TropicalSocialChoice.exists_gap
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:15:37.362922+00:00
-- url     : https://prove2.me/theorems/261e81cc-2252-42ca-aebc-7987c9dcf28a
-- title:
--   The gap hypothesis is satisfiable: if some coalition member is not pivotal, there is a
-- statement:
--   The gap hypothesis is satisfiable: if some coalition member is not pivotal, there is a
--   strictly positive `Δ` such that every non-pivotal member costs at least `min y + Δ`.
--
--   ```lean
--   theorem TropicalSocialChoice.exists_gap(s : Finset ι) (hs : s.Nonempty) (y : ι → ℝ)
--       (hne : (s \ pivotal s hs y).Nonempty) :
--       ∃ Δ : ℝ, 0 < Δ ∧ ∀ i ∈ s, i ∉ pivotal s hs y → s.inf' hs y + Δ ≤ y i := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/TropicalSocialChoiceDequantisation.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/TropicalSocialChoiceDequantisation.lean#L46

-- Thm stub generated from Probability/TropicalSocialChoiceDequantisation.lean
import Mathlib
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

theorem TropicalSocialChoice.exists_gap(s : Finset ι) (hs : s.Nonempty) (y : ι → ℝ)
    (hne : (s \ pivotal s hs y).Nonempty) :
    ∃ Δ : ℝ, 0 < Δ ∧ ∀ i ∈ s, i ∉ pivotal s hs y → s.inf' hs y + Δ ≤ y i := by sorry
