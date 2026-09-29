-- Prove2me | solution 1 for CutIndexedSingleton.cutEntropy_mono
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:44:43.581517+00:00
-- url     : https://prove2.me/submissions/01e29820-aa1f-4e50-a4c0-7a2c6f725f68

-- Sol generated from Novelty/CutIndexedEntropyMono.lean
import Mathlib
import Definitions.Def_Novelty_CutIndexedEntropy
import Definitions.Def_Novelty_CutIndexedEntropyMono
import Definitions.Def_Novelty_CutIndexedSingleton
import Theorems.Thm_CutIndexedSingleton_Real_negMulLog_sum_le
import Theorems.Thm_CutIndexedSingleton_cutProb_eq_sum_cutProb
import Theorems.Thm_CutIndexedSingleton_cutProb_nonneg

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










open CutIndexedSingleton in
theorem solution(C : Finset (Word n q)) {S T : Finset (Fin n)} (h : S ⊆ T) :
    cutEntropy C S ≤ cutEntropy C T := by
  classical
  calc cutEntropy C S
      = ∑ y : {i // i ∈ S} → Fin q, Real.negMulLog
          (∑ z ∈ (Finset.univ : Finset ({i // i ∈ T} → Fin q)).filter
            (fun z => restrictCut h z = y), cutProb C T z) := by
        unfold cutEntropy
        exact Finset.sum_congr rfl fun y _ => by rw [cutProb_eq_sum_cutProb h y]
    _ ≤ ∑ y : {i // i ∈ S} → Fin q,
          ∑ z ∈ (Finset.univ : Finset ({i // i ∈ T} → Fin q)).filter
            (fun z => restrictCut h z = y), Real.negMulLog (cutProb C T z) := by
        refine Finset.sum_le_sum fun y _ => ?_
        exact Real.negMulLog_sum_le _ _ fun z _ => cutProb_nonneg C T z
    _ = cutEntropy C T := by
        unfold cutEntropy
        exact Finset.sum_fiberwise (Finset.univ : Finset ({i // i ∈ T} → Fin q))
          (fun z => restrictCut h z) (fun z => Real.negMulLog (cutProb C T z))
