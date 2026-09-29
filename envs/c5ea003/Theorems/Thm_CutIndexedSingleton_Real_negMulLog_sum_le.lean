-- Prove2me | Theorems.Thm_CutIndexedSingleton_Real_negMulLog_sum_le
-- name    : CutIndexedSingleton.Real.negMulLog_sum_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:23:33.239908+00:00
-- url     : https://prove2.me/theorems/f6eca059-d0b5-4b16-9b67-d23085793c74
-- title:
--   Superadditivity of `negMulLog`.
-- statement:
--   **Superadditivity of `negMulLog`.**  For nonnegative summands,
--   `negMulLog (∑ aᵢ) ≤ ∑ negMulLog aᵢ`.
--
--   ```lean
--   theorem CutIndexedSingleton.Real.negMulLog_sum_le{ι : Type*} (s : Finset ι) (f : ι → ℝ)
--       (hf : ∀ i ∈ s, 0 ≤ f i) :
--       Real.negMulLog (∑ i ∈ s, f i) ≤ ∑ i ∈ s, Real.negMulLog (f i) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/CutIndexedEntropyMono.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/CutIndexedEntropyMono.lean#L51

-- Thm stub generated from Novelty/CutIndexedEntropyMono.lean
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

theorem CutIndexedSingleton.Real.negMulLog_sum_le{ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) :
    Real.negMulLog (∑ i ∈ s, f i) ≤ ∑ i ∈ s, Real.negMulLog (f i) := by sorry
