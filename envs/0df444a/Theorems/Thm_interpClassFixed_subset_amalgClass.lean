-- Prove2me | Theorems.Thm_interpClassFixed_subset_amalgClass
-- name    : interpClassFixed_subset_amalgClass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:41:32.063811+00:00
-- url     : https://prove2.me/theorems/5240d158-c44a-40b7-bdb5-35118d6f0c46
-- title:
--   interp Class Fixed subset amalg Class: interp Class Fixed subset amalg Class
-- statement:
--   Fixed-region interpolation is a subset of amalgamation with trivial projections.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Amalgamation.lean#L114-L126
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Amalgamation.lean#L114-L126

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Interpolation
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Amalgamation
set_option autoImplicit true
@[expose] public section
public section
universe u
open MeasureTheory

theorem interpClassFixed_subset_amalgClass
    {X : Type u}
    {Θ₁ Θ₂ : Type*}
    (e₁ : Θ₁ → Concept X Bool) (e₂ : Θ₂ → Concept X Bool)
    (A : Set X) :
    interpClassFixed (Set.range e₁) (Set.range e₂) A ⊆
      amalgClass (fun _ : Θ₁ => ()) (fun _ : Θ₂ => ())
        (fun p => piecewiseConcept A (e₁ p.1) (e₂ p.2)) := by sorry
