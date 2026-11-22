-- Prove2me | Theorems.Thm_growth_bounded_imp_vcdim_finite
-- name    : growth_bounded_imp_vcdim_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:34:53.595571+00:00
-- url     : https://prove2.me/theorems/e3141f1a-3492-4b4a-9cd9-4d4348463deb
-- title:
--   growth bounded imp vcdim finite: growth bounded imp vcdim finite
-- statement:
--   Growth function polynomially bounded → VCDim < ⊤.
--       Reverse direction: if GrowthFunction m ≤ ∑_{i≤d} C(m,i) for all m ≥ d,
--       then VCDim ≤ d (otherwise GrowthFunction = 2^m for m = VCDim > d).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Generalization/Core.lean#L2007-L2075
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Generalization/Core.lean#L2007-L2075

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

theorem growth_bounded_imp_vcdim_finite (X : Type u)
    (C : ConceptClass X Bool)
    (hgrowth : ∃ (d : ℕ), ∀ (m : ℕ), d ≤ m →
      GrowthFunction X C m ≤ ∑ i ∈ Finset.range (d + 1), Nat.choose m i) :
    VCDim X C < ⊤ := by sorry
