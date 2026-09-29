-- Prove2me | solution 1 for Probability.AdaptiveQS.keptInversionMass_le_inversionMass
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:34:15.669842+00:00
-- url     : https://prove2.me/submissions/b25af49d-6297-4ced-8366-3a3bf9d7d81f

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
theorem solution{s : Finset ι} {d r : ι → ℝ} (θ : ℝ) :
    keptInversionMass s d r θ ≤ inversionMass s d r := by
  set K := keepSet s d θ with hK
  set D := skipSet s d θ with hD
  have hstep : ∀ p ∈ D ×ˢ K,
      max (r p.1 - r p.2) 0 = if p ∈ discordantPairs s d r then r p.1 - r p.2 else 0 := by
    intro p hp
    rw [Finset.mem_product] at hp
    obtain ⟨hp1, hp2⟩ := hp
    rw [hD, skipSet, Finset.mem_filter] at hp1
    rw [hK, keepSet, Finset.mem_filter] at hp2
    have hd : d p.1 < d p.2 := lt_of_lt_of_le (not_le.mp hp1.2) hp2.2
    by_cases hlt : r p.2 < r p.1
    · have hmem : p ∈ discordantPairs s d r :=
        Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hp1.1, hp2.1⟩, ⟨hd, hlt⟩⟩
      rw [if_pos hmem, max_eq_left (by linarith)]
    · have hmem : p ∉ discordantPairs s d r := by
        intro hmem
        rw [discordantPairs, Finset.mem_filter] at hmem
        exact hlt hmem.2.2
      rw [if_neg hmem, max_eq_right (by linarith [not_lt.mp hlt])]
  calc keptInversionMass s d r θ
      = ∑ p ∈ D ×ˢ K, if p ∈ discordantPairs s d r then r p.1 - r p.2 else 0 :=
        Finset.sum_congr rfl hstep
    _ = ∑ p ∈ (D ×ˢ K).filter (fun p => p ∈ discordantPairs s d r), (r p.1 - r p.2) := by
        rw [Finset.sum_filter]
    _ ≤ inversionMass s d r := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
        · intro p hp
          exact (Finset.mem_filter.mp hp).2
        · intro p hp _
          rw [discordantPairs, Finset.mem_filter] at hp
          linarith [hp.2.2]
