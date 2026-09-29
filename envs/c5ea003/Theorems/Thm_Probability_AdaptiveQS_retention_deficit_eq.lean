-- Prove2me | Theorems.Thm_Probability_AdaptiveQS_retention_deficit_eq
-- name    : Probability.AdaptiveQS.retention_deficit_eq
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:54:46.850883+00:00
-- url     : https://prove2.me/theorems/62a52320-403e-412c-b82a-fee258139e2c
-- title:
--   The retention deficit is exactly a signed pair sum.
-- statement:
--   **The retention deficit is exactly a signed pair sum.**  For any splitting of the
--   targets into a retained and a deferred part, the deficit equals the total signed rate gap
--   over deferred × retained pairs.
--
--   ```lean
--   theorem Probability.AdaptiveQS.retention_deficit_eq{s K D : Finset ι} {r : ι → ℝ}
--       (hunion : K ∪ D = s) (hdisj : Disjoint K D) :
--       (K.card : ℝ) * (∑ i ∈ s, r i) - (s.card : ℝ) * (∑ i ∈ K, r i)
--         = ∑ p ∈ D ×ˢ K, (r p.1 - r p.2) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/AdaptiveQSInversionMass.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/AdaptiveQSInversionMass.lean#L175

-- Thm stub generated from Probability/AdaptiveQSInversionMass.lean
import Mathlib
import Definitions.Def_Probability_AdaptiveQSAllocation
import Definitions.Def_Probability_AdaptiveQSDiscordance
import Definitions.Def_Probability_AdaptiveQSInversionMass
import Definitions.Def_Probability_AdaptiveQSSkipFlip
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# The inversion-mass refinement of the discordance budget

`AdaptiveQSDiscordance.lean` proved a *linear* budget for an arbitrary dial: the yield
retained by a threshold skip falls short of the work-proportional amount by at most
`M · |Disc|`, where `M` is the maximal rate and `Disc` the dial's inversion set.  That
bound charges the global maximum `M` to every inversion, so it is tight only when every
inversion pits a maximal target against a null one — which is exactly the situation the
measured run (`89.5%` retention at `71.7%` of the work) is *not* in.

This file closes the corresponding open direction ("Inversion-Mass Refinement of the
Discordance Budget") by charging each inversion its *actual* rate gap:

* `sum_le_of_positive_part_penalty` — the sharpened separation engine.  No boundedness and
  no nonnegativity hypotheses at all: for any splitting `s = K ⊔ D`,
  `|K| · Σ_s r ≤ |s| · Σ_K r + Σ_{(j,i) ∈ D×K} (r j − r i)⁺`.
* `inversionMass` — the total rate gap carried by the dial's inversions.
* `retention_of_inversion_mass`, `throughput_le_of_inversion_mass` — the refined budget in
  retention and in throughput form.
* `inversionMass_le_max_mul_card` — the refinement dominates: the inversion mass is at most
  `M · |Disc|`, so the new bound is never weaker than the old one, and
  `retention_of_discordance_of_inversion_mass` re-derives the old bound from the new one.
* `inversionMass_le_gap_mul_card` — a scale-free form: if every inversion has gap at most
  `g`, the whole penalty is at most `g · |Disc|`.
* `inversionMass_eq_zero_iff_concordant` — the penalty vanishes exactly for concordant
  dials, so the refined bound is an equality-preserving strengthening.
* `retention_deficit_eq`, `retention_deficit_eq_mass_difference` — the *exact* two-sided
  decomposition behind the budget: the retention deficit equals the inversion mass the
  threshold pays minus the concordance mass it earns, so the one-sided bound is tight
  precisely when the dial is never right about a deferred/retained pair.
* `retention_of_inversion_mass_sharp` — the resulting sharpened budget.
* Lab note `labnote_inversion_mass_strictly_better`: an explicit three-target dial with one
  inversion, where the refined penalty is `1` and the old penalty is `10`.
-/

open Probability.AdaptiveQS

open Finset

variable {ι : Type*} [DecidableEq ι]

/-! ## The sharpened separation engine -/


/-! ## The inversion mass -/








/-! ## The exact two-sided decomposition

The engine above is an inequality only because it discards the pairs the dial gets right.
Keeping them gives an *identity*, and hence a characterisation of when the budget is
tight. -/

theorem Probability.AdaptiveQS.retention_deficit_eq{s K D : Finset ι} {r : ι → ℝ}
    (hunion : K ∪ D = s) (hdisj : Disjoint K D) :
    (K.card : ℝ) * (∑ i ∈ s, r i) - (s.card : ℝ) * (∑ i ∈ K, r i)
      = ∑ p ∈ D ×ˢ K, (r p.1 - r p.2) := by sorry
