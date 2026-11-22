-- Prove2me | Theorems.Thm_optimal_mistake_bound_eq_ldim
-- name    : optimal_mistake_bound_eq_ldim
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:40:25.227357+00:00
-- url     : https://prove2.me/theorems/6db1a8a7-3b18-404e-9bdb-2595644ae8f4
-- title:
--   optimal mistake bound eq ldim: optimal mistake bound eq ldim
-- statement:
--   The optimal mistake bound equals the Littlestone dimension (for nonempty C).
--       Path B: OptimalMistakeBound : WithTop ℕ, LittlestoneDim : WithBot (WithTop ℕ).
--       For nonempty C, LittlestoneDim ≥ 0, so the coercion ↑(OptimalMistakeBound) works.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Theorem/Online.lean#L436-L478
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Theorem/Online.lean#L436-L478

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_GameInfra
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Definitions.Def_LeanPool_FormalLearningTheory_Theorem_Online
set_option autoImplicit true
@[expose] public section
public section

theorem optimal_mistake_bound_eq_ldim (X : Type)
    (C : ConceptClass X Bool) (hne : C.Nonempty) :
    (↑(OptimalMistakeBound X C) : WithBot (WithTop ℕ)) = LittlestoneDim X C := by sorry
