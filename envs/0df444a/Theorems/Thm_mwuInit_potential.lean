-- Prove2me | Theorems.Thm_mwuInit_potential
-- name    : mwuInit_potential
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:32:17.823582+00:00
-- url     : https://prove2.me/theorems/521de762-4bc6-40dd-8af5-b2135b3c739b
-- title:
--   mwu Init potential: mwu Init potential
-- statement:
--   The mwu Init potential construction uses the mwu Init potential property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/PureMath/ApproxMinimax.lean#L253-L255
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/PureMath/ApproxMinimax.lean#L253-L255

module
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_KLDivergence
public import Mathlib.Algebra.BigOperators.Field
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_ApproxMinimax
set_option autoImplicit true
@[expose] public section
public section
open Finset
noncomputable section

theorem mwuInit_potential (C : Type*) [Fintype C] :
    (mwuInit C).potential = Fintype.card C := by sorry
