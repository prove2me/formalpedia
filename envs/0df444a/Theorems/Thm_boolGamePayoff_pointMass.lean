-- Prove2me | Theorems.Thm_boolGamePayoff_pointMass
-- name    : boolGamePayoff_pointMass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:32:30.601792+00:00
-- url     : https://prove2.me/theorems/c7677c00-1137-4127-afef-11331848498d
-- title:
--   bool Game Payoff point Mass: bool Game Payoff point Mass
-- statement:
--   Point mass payoff equals the game value at that row-column pair.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/PureMath/ApproxMinimax.lean#L109-L118
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/PureMath/ApproxMinimax.lean#L109-L118

module
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_KLDivergence
public import Mathlib.Algebra.BigOperators.Field
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_ApproxMinimax
set_option autoImplicit true
@[expose] public section
public section
open Finset
noncomputable section

theorem boolGamePayoff_pointMass {R C : Type*} [Fintype R] [DecidableEq R]
    (M : R → C → Bool) (r₀ : R) (c : C) :
    boolGamePayoff M (pointMassPMF r₀) c = if M r₀ c then 1 else 0 := by sorry
