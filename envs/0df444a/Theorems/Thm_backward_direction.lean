-- Prove2me | Theorems.Thm_backward_direction
-- name    : backward_direction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:36:46.5139+00:00
-- url     : https://prove2.me/theorems/6e7a501e-3b39-47c0-a3c5-8ff9280a202a
-- title:
--   backward direction: backward direction
-- statement:
--   Backward direction: LittlestoneDim < ⊤ → OnlineLearnable.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Theorem/Online.lean#L387-L408
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Theorem/Online.lean#L387-L408

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_GameInfra
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Definitions.Def_LeanPool_FormalLearningTheory_Theorem_Online
set_option autoImplicit true
@[expose] public section
public section

theorem backward_direction (X : Type) (C : ConceptClass X Bool) :
    LittlestoneDim X C < ⊤ → OnlineLearnable X Bool C := by sorry
