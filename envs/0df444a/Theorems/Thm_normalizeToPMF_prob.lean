-- Prove2me | Theorems.Thm_normalizeToPMF_prob
-- name    : normalizeToPMF_prob
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:32:08.694072+00:00
-- url     : https://prove2.me/theorems/0551bb45-784f-488a-87a8-9803f634877a
-- title:
--   normalize To PMF prob: normalize To PMF prob
-- statement:
--   The normalize To PMF prob construction uses the normalize To PMF prob property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/PureMath/ApproxMinimax.lean#L57-L59
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/PureMath/ApproxMinimax.lean#L57-L59

module
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_KLDivergence
public import Mathlib.Algebra.BigOperators.Field
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_ApproxMinimax
set_option autoImplicit true
@[expose] public section
public section
open Finset
noncomputable section

theorem normalizeToPMF_prob {C : Type*} [Fintype C] [Nonempty C]
    (w : C → ℝ) (hw : ∀ c, 0 < w c) (c : C) :
    (normalizeToPMF w hw).prob c = w c / ∑ c' : C, w c' := by sorry
