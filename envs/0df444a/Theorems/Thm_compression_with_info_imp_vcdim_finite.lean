-- Prove2me | Theorems.Thm_compression_with_info_imp_vcdim_finite
-- name    : compression_with_info_imp_vcdim_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:35:58.546477+00:00
-- url     : https://prove2.me/theorems/b11d16d8-4c6d-4188-b5ec-9497108b5c05
-- title:
--   compression with info imp vcdim finite: compression with info imp vcdim finite
-- statement:
--   Compression with side info implies finite VC dimension.
--       Proof by pigeonhole: compress is injective on C-realizable labelings
--       (by correctness), but compressed outputs form a bounded set.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Compression.lean#L1162-L1263
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Compression.lean#L1162-L1263

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Structures
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_FiniteVCApprox
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Tail
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_FiniteSupportUC
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Compression
set_option autoImplicit true
@[expose] public section
public section
open Finset
noncomputable section
universe u
attribute [local instance] Classical.propDecidable

theorem compression_with_info_imp_vcdim_finite
    (X : Type u) (C : ConceptClass X Bool)
    (hcomp : ∃ (k : ℕ) (cs : CompressionSchemeWithInfo X Bool C), cs.size = k) :
    VCDim X C < ⊤ := by sorry
