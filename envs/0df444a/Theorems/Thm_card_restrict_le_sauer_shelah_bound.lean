-- Prove2me | Theorems.Thm_card_restrict_le_sauer_shelah_bound
-- name    : card_restrict_le_sauer_shelah_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:36:18.301656+00:00
-- url     : https://prove2.me/theorems/83555cca-b9a5-41d2-81e0-1e0771c97922
-- title:
--   card restrict le sauer shelah bound: card restrict le sauer shelah bound
-- statement:
--   The card restrict le sauer shelah bound construction uses the card restrict le sauer shelah bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Bridge.lean#L389-L421
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Bridge.lean#L389-L421

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Data
public import Mathlib.Combinatorics.SetFamily.Shatter
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Ordinal
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Structures
public import Definitions.Def_LeanPool_FormalLearningTheory_Learner_Bayesian
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Definitions.Def_LeanPool_FormalLearningTheory_Bridge
set_option autoImplicit true
@[expose] public section
public section
universe u v

theorem card_restrict_le_sauer_shelah_bound {X : Type u} [Fintype X] [DecidableEq X]
    (C : Finset (X → Bool)) (S : Finset X)
    (d : ℕ) (hd : Finset.vcDim (conceptClassToFinsetFamily C) = d) :
    (restrictConceptClass C S).card ≤
      ∑ i ∈ Finset.range (d + 1), Nat.choose S.card i := by sorry
