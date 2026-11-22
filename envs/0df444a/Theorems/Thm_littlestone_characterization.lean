-- Prove2me | Theorems.Thm_littlestone_characterization
-- name    : littlestone_characterization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:40:23.981249+00:00
-- url     : https://prove2.me/theorems/960a4c02-ab63-4652-99ff-590d26d15c98
-- title:
--   littlestone characterization: littlestone characterization
-- statement:
--   Littlestone characterization: C is online-learnable iff LittlestoneDim(C) < ∞.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Theorem/Online.lean#L415-L418
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Theorem/Online.lean#L415-L418

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_GameInfra
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Definitions.Def_LeanPool_FormalLearningTheory_Theorem_Online
set_option autoImplicit true
@[expose] public section
public section

theorem littlestone_characterization (X : Type)
    (C : ConceptClass X Bool) :
    OnlineLearnable X Bool C ↔ LittlestoneDim X C < ⊤ := by sorry
