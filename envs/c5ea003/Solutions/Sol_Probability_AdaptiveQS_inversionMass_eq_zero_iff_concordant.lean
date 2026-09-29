-- Prove2me | solution 1 for Probability.AdaptiveQS.inversionMass_eq_zero_iff_concordant
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:34:15.081419+00:00
-- url     : https://prove2.me/submissions/5e2a4820-3649-4e7f-9172-b96a678e6405

-- Sol generated from Probability/AdaptiveQSInversionMass.lean
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








/-! ## Lab note — the refinement is strictly better

Three targets with rates `(10, 3, 2)` and a dial that ranks them `(10, 2, 3)`: the dial is
right about the big target and merely swaps the two nearly equal small ones.  There is
exactly one inversion, so the old penalty is `M · |Disc| = 10`, while the refined penalty
is the actual gap `3 − 2 = 1`.  All numbers below are proved. -/







open Probability.AdaptiveQS in
omit [DecidableEq ι] in
theorem solution(s : Finset ι) (d r : ι → ℝ) :
    inversionMass s d r = 0 ↔ discordantPairs s d r = ∅ := by
  constructor
  · intro h
    rw [Finset.eq_empty_iff_forall_notMem]
    intro p hp
    have hpos : 0 < r p.1 - r p.2 := by
      rw [discordantPairs, Finset.mem_filter] at hp
      linarith [hp.2.2]
    have hle : r p.1 - r p.2 ≤ inversionMass s d r := by
      refine Finset.single_le_sum (f := fun q => r q.1 - r q.2) (fun q hq => ?_) hp
      rw [discordantPairs, Finset.mem_filter] at hq
      linarith [hq.2.2]
    rw [h] at hle
    linarith
  · intro h
    rw [inversionMass, h, Finset.sum_empty]
