-- Prove2me | Theorems.Thm_vcdim_to_ordinal_vcdim
-- name    : vcdim_to_ordinal_vcdim
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:39:22.963821+00:00
-- url     : https://prove2.me/theorems/d2a921c0-bdde-4836-96db-c8238090f32d
-- title:
--   vcdim to ordinal vcdim: vcdim to ordinal vcdim
-- statement:
--   VCDim embeds into OrdinalVCDim via this bridge.
--       Γ₂₇ RESOLVED: uniform ω-bound BddAbove (from Ordinal.lean) makes le_ciSup_of_le
--       work for all ordinal-valued nat-cast iSup. The bridge is paradigm-invariant.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Bridge.lean#L528-L579
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Bridge.lean#L528-L579

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Data
public import Mathlib.Combinatorics.SetFamily.Shatter
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Ordinal
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Structures
public import Definitions.Def_LeanPool_FormalLearningTheory_Learner_Bayesian
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Definitions.Def_LeanPool_FormalLearningTheory_Bridge
set_option autoImplicit true
@[expose] public section
public section
universe u v

theorem vcdim_to_ordinal_vcdim (X : Type u)
    (C : ConceptClass X Bool) :
    withTopNatToOrdinal (VCDim X C) ≤ OrdinalVCDim X C := by sorry
