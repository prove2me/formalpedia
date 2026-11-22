-- Prove2me | Theorems.Thm_forward_direction
-- name    : forward_direction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:34:15.453328+00:00
-- url     : https://prove2.me/theorems/216824ba-3cc9-42f1-a5bc-92400af3fe88
-- title:
--   forward direction: forward direction
-- statement:
--   Forward direction: OnlineLearnable → LittlestoneDim < ⊤
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Theorem/Online.lean#L32-L54
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Theorem/Online.lean#L32-L54

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_GameInfra
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Definitions.Def_LeanPool_FormalLearningTheory_Theorem_Online
set_option autoImplicit true
@[expose] public section
public section

theorem forward_direction (X : Type) (C : ConceptClass X Bool) :
    OnlineLearnable X Bool C → LittlestoneDim X C < ⊤ := by sorry
