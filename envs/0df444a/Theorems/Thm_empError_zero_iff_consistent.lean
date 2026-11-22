-- Prove2me | Theorems.Thm_empError_zero_iff_consistent
-- name    : empError_zero_iff_consistent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:34:18.355215+00:00
-- url     : https://prove2.me/theorems/e5ca416e-afa6-439c-bd5d-785c49aa46ff
-- title:
--   emp Error zero iff consistent: emp Error zero iff consistent
-- statement:
--   EmpiricalError with a faithful loss is zero iff consistent.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Generalization/Core.lean#L327-L355
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Generalization/Core.lean#L327-L355

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_Online
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_PAC
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Structures
public import Mathlib.Combinatorics.SetFamily.Shatter
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
set_option autoImplicit true
@[expose] public section
public section
universe u v

theorem empError_zero_iff_consistent {X : Type u} {Y : Type v} [DecidableEq Y]
    (h : Concept X Y) {m : ℕ} (hm : 0 < m) (S : Fin m → X × Y)
    (loss : LossFunction Y) (hfaith : IsFaithfulLoss loss)
    (hloss_nonneg : ∀ y₁ y₂, 0 ≤ loss y₁ y₂) :
    EmpiricalError X Y h S loss = 0 ↔ IsConsistentWith X Y h S := by sorry
