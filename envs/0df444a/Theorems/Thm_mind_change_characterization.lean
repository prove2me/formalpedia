-- Prove2me | Theorems.Thm_mind_change_characterization
-- name    : mind_change_characterization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:33:18.870236+00:00
-- url     : https://prove2.me/theorems/4ef8fefd-aca0-446a-b865-0094b9f46a00
-- title:
--   mind change characterization: mind change characterization
-- statement:
--   Mind change characterization: EX-learnable iff every text presentation has
--       finite mind change ordinal. With correctness encoded in MindChangeOrdinal,
--       `< omega0` captures both correct convergence and finite mind changes.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Theorem/Gold.lean#L213-L265
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Theorem/Gold.lean#L213-L265

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_Gold
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_MindChange
public import Mathlib.SetTheory.Ordinal.Arithmetic
public import Definitions.Def_LeanPool_FormalLearningTheory_Theorem_Gold
set_option autoImplicit true
@[expose] public section
public section
universe u v

theorem mind_change_characterization (X : Type u)
    (C : ConceptClass X Bool) :
    EXLearnable X C ↔
      ∃ (L : GoldLearner X Bool),
        ∀ (c : Concept X Bool), c ∈ C →
          ∀ (T : TextPresentation X c),
            MindChangeOrdinal X L c T.toDataStream < Ordinal.omega0 := by sorry
