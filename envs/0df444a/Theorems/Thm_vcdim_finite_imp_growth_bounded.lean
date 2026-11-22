-- Prove2me | Theorems.Thm_vcdim_finite_imp_growth_bounded
-- name    : vcdim_finite_imp_growth_bounded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:33:50.959693+00:00
-- url     : https://prove2.me/theorems/25565e0b-245a-4d60-9e01-af0f48715a25
-- title:
--   vcdim finite imp growth bounded: vcdim finite imp growth bounded
-- statement:
--   VCDim < ⊤ → growth function polynomially bounded by partial binomial sum.
--       Forward direction of fundamental_theorem conjunct 5.
--       Uses Sauer-Shelah: GrowthFunction(m) ≤ ∑_{i≤d} C(m,i) where d = VCDim.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Generalization/Core.lean#L586-L700
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Generalization/Core.lean#L586-L700

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

theorem vcdim_finite_imp_growth_bounded (X : Type u)
    (C : ConceptClass X Bool) (hC : VCDim X C < ⊤) :
    ∃ (d : ℕ), ∀ (m : ℕ), d ≤ m →
      GrowthFunction X C m ≤ ∑ i ∈ Finset.range (d + 1), Nat.choose m i := by sorry
