-- Prove2me | Theorems.Thm_boolGamePayoff_le_one
-- name    : boolGamePayoff_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:32:11.87919+00:00
-- url     : https://prove2.me/theorems/5c7f27a6-b513-4457-b3c1-3e6cf1394a41
-- title:
--   bool Game Payoff le one: bool Game Payoff le one
-- statement:
--   The bool Game Payoff le one construction uses the bool Game Payoff le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/PureMath/ApproxMinimax.lean#L100-L106
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/PureMath/ApproxMinimax.lean#L100-L106

module
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_KLDivergence
public import Mathlib.Algebra.BigOperators.Field
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_ApproxMinimax
set_option autoImplicit true
@[expose] public section
public section
open Finset
noncomputable section

theorem boolGamePayoff_le_one {R C : Type*} [Fintype R]
    (M : R → C → Bool) (p : FinitePMF R) (c : C) :
    boolGamePayoff M p c ≤ 1 := by sorry
