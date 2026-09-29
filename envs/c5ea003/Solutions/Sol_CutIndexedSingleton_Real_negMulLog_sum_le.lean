-- Prove2me | solution 1 for CutIndexedSingleton.Real.negMulLog_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:20:39.885744+00:00
-- url     : https://prove2.me/submissions/2f74f95a-40cf-4aa9-9643-2054560e5667

-- Sol generated from Novelty/CutIndexedEntropyMono.lean
import Mathlib
import Definitions.Def_Novelty_CutIndexedEntropy
import Definitions.Def_Novelty_CutIndexedEntropyMono

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
theorem solution{ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) :
    Real.negMulLog (∑ i ∈ s, f i) ≤ ∑ i ∈ s, Real.negMulLog (f i) := by
  classical
  have hA0 : 0 ≤ ∑ i ∈ s, f i := Finset.sum_nonneg hf
  rcases eq_or_lt_of_le hA0 with h | h
  · have hzero : ∀ i ∈ s, f i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg hf).mp h.symm
    have hl : Real.negMulLog (∑ i ∈ s, f i) = 0 := by
      rw [← h, Real.negMulLog_zero]
    have hr : ∑ i ∈ s, Real.negMulLog (f i) = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      rw [hzero i hi, Real.negMulLog_zero]
    rw [hl, hr]
  · have key : ∀ i ∈ s, -f i * Real.log (∑ j ∈ s, f j) ≤ Real.negMulLog (f i) := by
      intro i hi
      rcases eq_or_lt_of_le (hf i hi) with h0 | h0
      · rw [← h0]
        simp
      · have hle : f i ≤ ∑ j ∈ s, f j := Finset.single_le_sum hf hi
        have hlog : Real.log (f i) ≤ Real.log (∑ j ∈ s, f j) := Real.log_le_log h0 hle
        simp only [Real.negMulLog_def]
        nlinarith
    have hsum : Real.negMulLog (∑ i ∈ s, f i)
        = ∑ i ∈ s, (-f i * Real.log (∑ j ∈ s, f j)) := by
      simp only [Real.negMulLog_def, ← Finset.sum_neg_distrib, ← Finset.sum_mul]
    rw [hsum]
    exact Finset.sum_le_sum key
