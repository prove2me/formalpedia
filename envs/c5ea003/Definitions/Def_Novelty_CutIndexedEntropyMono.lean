-- Prove2me | Definitions.Def_Novelty_CutIndexedEntropyMono
-- name    : Novelty_CutIndexedEntropyMono
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:11:49.528032+00:00
-- url     : https://prove2.me/theorems/3f1ca896-0096-44eb-ba05-7589b33d04fa
-- title:
--   Aether Catalog definitions — Novelty_CutIndexedEntropyMono
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.CutIndexedEntropyMono`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/CutIndexedEntropyMono.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_CutIndexedEntropy

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

namespace CutIndexedSingleton

variable {n q : ℕ}


/-- The restriction of a pattern on a cut to a sub-cut. -/
def restrictCut {S T : Finset (Fin n)} (h : S ⊆ T) (z : {i // i ∈ T} → Fin q) :
    {i // i ∈ S} → Fin q := fun i => z ⟨i.1, h i.2⟩







end CutIndexedSingleton


