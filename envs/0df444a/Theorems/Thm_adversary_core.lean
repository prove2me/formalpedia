-- Prove2me | Theorems.Thm_adversary_core
-- name    : adversary_core
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:33:06.210839+00:00
-- url     : https://prove2.me/theorems/3639df9f-6251-4b3a-a01d-06241fdfcb87
-- title:
--   adversary core: adversary core
-- statement:
--   Core adversary lemma.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/GameInfra.lean#L87-L114
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/GameInfra.lean#L87-L114

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_Online
public import Mathlib.Order.Lattice.Nat
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_GameInfra
set_option autoImplicit true
@[expose] public section
public section

theorem adversary_core {X : Type}
    (L : OnlineLearner X Bool) (s : L.State)
    {C : ConceptClass X Bool} {n : ℕ}
    (T : LTree X n) (hT : T.isShattered C) (hne : C.Nonempty) :
    ∃ (seq : List X) (c : X → Bool), c ∈ C ∧
      L.mistakesFrom s c seq = n := by sorry
