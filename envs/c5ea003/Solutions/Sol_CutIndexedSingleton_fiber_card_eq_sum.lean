-- Prove2me | solution 1 for CutIndexedSingleton.fiber_card_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:28:47.754972+00:00
-- url     : https://prove2.me/submissions/0e0b84d3-07a8-4b0e-a37e-571e8a0b7278

-- Sol generated from Novelty/CutIndexedEntropyMono.lean
import Mathlib
import Definitions.Def_Novelty_CutIndexedEntropy
import Definitions.Def_Novelty_CutIndexedEntropyMono
import Definitions.Def_Novelty_CutIndexedSingleton

/-!
# Cut-indexed defects V: the entropy profile is a monotone cut datum

Files I–III bound the cut entropy from above.  This file establishes the missing
*structural* property of the profile `S ↦ cutEntropy C S`: it is **monotone**
along the lattice of cuts.  Together with `cutEntropy_le_card_mul_log` this says
that the entropy profile of a codebook is itself a (real-valued) cut datum in the
sense of file I: it starts at `0`, never decreases, and never exceeds `|S| log q`.

## Main results

* `Real.negMulLog_sum_le` : **superadditivity of `negMulLog`**,
  `negMulLog (∑ aᵢ) ≤ ∑ negMulLog aᵢ` for nonnegative `aᵢ` — the analytic engine;
* `cutProb_eq_sum_cutProb` : the marginal on a sub-cut is the coarse-graining of
  the marginal on the larger cut;
* `cutEntropy_mono` : **`S ⊆ T → cutEntropy C S ≤ cutEntropy C T`**;
* `cutEntropy_empty` : the entropy of the empty cut vanishes;
* `cutEntropy_nonneg'` : hence the profile is nonnegative even without invoking
  the probability-vector bound.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): the classical cut-rank axioms of `CutData`
(`rank ∅ ≤ 1`, monotone, one-site growth `≤ q`) should have an exact entropic
mirror (`H ∅ = 0`, monotone, one-site growth `≤ log q`).  If all three mirror
axioms hold, the abstract Singleton argument of file I can be rerun verbatim in
the entropic category.

Experiment (Experimenter): axioms one and two are proved here.  Monotonicity is
*not* a formal consequence of the counting monotonicity `cutRank_mono`: entropy
can decrease under coarse-graining of the alphabet in general, and what saves the
day is that the coarse-graining here is *deterministic* — the marginal on `S` is
obtained by summing the fibres of the marginal on `T`, and `negMulLog` is
superadditive on nonnegatives.

Analysis (Analyst): the third mirror axiom, `H(S ∪ {a}) ≤ H(S) + log q`, is the
Shannon chain rule, and it is *not* derivable from the two axioms proved here;
formalising the conditional-entropy decomposition is the concrete next step
recorded as Direction 2 of `FUTURE_DIRECTIONS.md`.  Note the contrast with the
negative result `Examples.cutRank_not_submodular`: the entropic profile is
strictly better behaved than the rank profile, which is exactly why the entropy
version of the Singleton defect detects MDS at a single cut.
-/

open Finset

open CutIndexedSingleton

variable {n q : ℕ}



@[simp] lemma restrictCut_proj {S T : Finset (Fin n)} (h : S ⊆ T) (c : Word n q) :
    restrictCut h (proj T c) = proj S c := rfl







open CutIndexedSingleton in
theorem solution{C : Finset (Word n q)} {S T : Finset (Fin n)} (h : S ⊆ T)
    (y : {i // i ∈ S} → Fin q) :
    (fiber C S y).card
      = ∑ z ∈ (Finset.univ : Finset ({i // i ∈ T} → Fin q)).filter
          (fun z => restrictCut h z = y), (fiber C T z).card := by
  classical
  have hmaps : Set.MapsTo (proj T) (fiber C S y : Set (Word n q))
      ((Finset.univ.filter (fun z : {i // i ∈ T} → Fin q => restrictCut h z = y) :
        Finset _) : Set _) := by
    intro c hc
    have hc' : proj S c = y := (Finset.mem_filter.mp hc).2
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and]
    rw [restrictCut_proj h c, hc']
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  refine Finset.sum_congr rfl fun z hz => ?_
  have hzy : restrictCut h z = y := (Finset.mem_filter.mp hz).2
  congr 1
  ext c
  simp only [fiber, Finset.mem_filter]
  constructor
  · rintro ⟨⟨hcC, -⟩, hcT⟩
    exact ⟨hcC, hcT⟩
  · rintro ⟨hcC, hcT⟩
    refine ⟨⟨hcC, ?_⟩, hcT⟩
    rw [← restrictCut_proj h c, hcT, hzy]
