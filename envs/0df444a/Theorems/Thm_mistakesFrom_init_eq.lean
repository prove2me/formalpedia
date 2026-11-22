-- Prove2me | Theorems.Thm_mistakesFrom_init_eq
-- name    : mistakesFrom_init_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:33:07.864402+00:00
-- url     : https://prove2.me/theorems/296833d5-c509-4a3f-80a5-e5c5c338ed08
-- title:
--   mistakes From init eq: mistakes From init eq
-- statement:
--   Relate mistakesFrom to the original mistakes function.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/GameInfra.lean#L117-L120
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/GameInfra.lean#L117-L120

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_Online
public import Mathlib.Order.Lattice.Nat
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_GameInfra
set_option autoImplicit true
@[expose] public section
public section

theorem mistakesFrom_init_eq {X : Type}
    (L : OnlineLearner X Bool) (c : X → Bool) (seq : List X) :
    L.mistakesFrom L.init c seq = L.mistakes c seq := by sorry
