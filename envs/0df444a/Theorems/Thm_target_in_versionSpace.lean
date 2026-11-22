-- Prove2me | Theorems.Thm_target_in_versionSpace
-- name    : target_in_versionSpace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:33:08.986095+00:00
-- url     : https://prove2.me/theorems/e63c4a65-f354-420d-8500-f4979985fd18
-- title:
--   target in version Space: target in version Space
-- statement:
--   Target stays in version space.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/GameInfra.lean#L182-L186
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/GameInfra.lean#L182-L186

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_Online
public import Mathlib.Order.Lattice.Nat
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_GameInfra
set_option autoImplicit true
@[expose] public section
public section

theorem target_in_versionSpace {X : Type} {C : ConceptClass X Bool}
    {c : X → Bool} (hcC : c ∈ C) {history : List (X × Bool)}
    (hcons : ∀ p ∈ history, c p.1 = p.2) :
    c ∈ versionSpace C history := by sorry
