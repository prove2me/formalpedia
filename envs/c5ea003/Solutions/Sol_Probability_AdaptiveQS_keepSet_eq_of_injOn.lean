-- Prove2me | solution 1 for Probability.AdaptiveQS.keepSet_eq_of_injOn
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:29:44.600966+00:00
-- url     : https://prove2.me/submissions/831a91e8-4494-4e72-b7e1-f67d0ab31b5f

-- Sol generated from Probability/AdaptiveQSTieSlack.lean
import Mathlib
import Definitions.Def_Probability_AdaptiveQSAllocation
import Definitions.Def_Probability_AdaptiveQSPrefixOptimality
import Definitions.Def_Probability_AdaptiveQSResidueRate
import Definitions.Def_Probability_AdaptiveQSSkipFlip
import Definitions.Def_Probability_AdaptiveQSTieSlack
import Theorems.Thm_Probability_AdaptiveQS_separated_subset_keepSet
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# Tie-multiplicity slack of threshold deferral, and its arithmetic vanishing

`AdaptiveQSPrefixOptimality.lean` collapsed the deployment policy space: the minimum-work
quota-feasible schedule can always be taken *separated*, and a separated schedule sits
inside the dial threshold set `keepSet s r θ` at `θ = ` its own minimal rate.  That left
exactly one gap, recorded as the open direction "Tie-Multiplicity Slack of Threshold
Deferral": the threshold set retains *every* target whose rate equals `θ`, so it can be
strictly larger than the minimal schedule.

This file closes that gap.

* `tieClass` — the targets sitting exactly on the threshold.
* `keepSet_sdiff_eq_tieClass_sdiff` — the excess of the threshold set over a separated
  schedule is *exactly* the tie class outside it (an equality of sets, not a bound).
* `keepSet_card_eq_add_tie_slack` — hence the cardinality identity
  `|keepSet| = |T| + |tieClass \ T|`: the extra work done by the threshold policy is the
  tie multiplicity, nothing more.
* `keepSet_eq_of_injOn` — if the rate dial is injective on the targets there are no ties,
  and the threshold policy reproduces the minimal schedule *on the nose*.
* `periodRate_injOn_admissible` — the arithmetic input: on a factor base of admissible odd
  primes the exact rate `2/p` is injective, because `p ↦ 2/p` is.
* `factorBase_threshold_exactly_minimal` — the capstone: on such a factor base, whenever a
  relation quota is attainable there is a threshold whose retained set meets the quota, has
  the *minimum possible* cardinality among all quota-feasible schedules, and has throughput
  at least that of sieving the whole factor base.
* Lab note `labnote_tie_slack_is_one`: a three-target instance with a genuine tie, where the
  threshold policy does one unit of work more than the optimum — showing the slack term is
  not vacuous and that injectivity is doing real work.
-/

open Probability.AdaptiveQS

open Finset

variable {ι : Type*} [DecidableEq ι]

/-! ## The tie class of a threshold -/


/-- **The excess of a threshold over a separated schedule is exactly its tie class.**
If `T` is separated in `s`, then the targets that the threshold at `θ = min_T r` retains
beyond `T` are precisely the targets outside `T` whose rate equals `θ`. -/
theorem keepSet_sdiff_eq_tieClass_sdiff {s T : Finset ι} {r : ι → ℝ}
    (hT : T.Nonempty) (hsep : Separated s T r) :
    keepSet s r (T.inf' hT r) \ T = tieClass s r (T.inf' hT r) \ T := by
  ext i
  simp only [Finset.mem_sdiff, keepSet, tieClass, Finset.mem_filter]
  constructor
  · rintro ⟨⟨his, hθi⟩, hiT⟩
    refine ⟨⟨his, le_antisymm ?_ hθi⟩, hiT⟩
    obtain ⟨t, htT, ht⟩ := Finset.exists_mem_eq_inf' hT r
    rw [ht]
    exact hsep t htT i his hiT
  · rintro ⟨⟨his, hri⟩, hiT⟩
    exact ⟨⟨his, le_of_eq hri.symm⟩, hiT⟩



/-! ## The arithmetic case: rates `2/p` are pairwise distinct -/




/-! ## Lab note — the slack is real when rates tie

Rates `(3, 3, 1)` on the three targets `{0, 1, 2}` and quota `Q = 3`.  The minimum-work
schedule is a single target, but the threshold at `θ = 3` must retain both targets of rate
`3`: the tie multiplicity is `1`, and the threshold policy does one unit of work more than
the optimum.  This is exactly the term that `keepSet_card_eq_add_tie_slack` isolates, and
that `periodRate_injOn_admissible` rules out arithmetically. -/





open Probability.AdaptiveQS in
theorem solution{s T : Finset ι} {r : ι → ℝ} (hTs : T ⊆ s)
    (hT : T.Nonempty) (hsep : Separated s T r) (hinj : Set.InjOn r s) :
    keepSet s r (T.inf' hT r) = T := by
  have hsub : T ⊆ keepSet s r (T.inf' hT r) := separated_subset_keepSet hTs hT
  refine Finset.Subset.antisymm ?_ hsub
  intro i hi
  by_contra hiT
  have hmem : i ∈ keepSet s r (T.inf' hT r) \ T := Finset.mem_sdiff.mpr ⟨hi, hiT⟩
  rw [keepSet_sdiff_eq_tieClass_sdiff hT hsep] at hmem
  obtain ⟨hi', hiT'⟩ := Finset.mem_sdiff.mp hmem
  rw [tieClass, Finset.mem_filter] at hi'
  obtain ⟨t, htT, ht⟩ := Finset.exists_mem_eq_inf' hT r
  have : i = t := hinj hi'.1 (hTs htT) (by rw [hi'.2, ht])
  exact hiT (this ▸ htT)
