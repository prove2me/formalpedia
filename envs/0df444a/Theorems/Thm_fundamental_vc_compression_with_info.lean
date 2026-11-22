-- Prove2me | Theorems.Thm_fundamental_vc_compression_with_info
-- name    : fundamental_vc_compression_with_info
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:36:09.323793+00:00
-- url     : https://prove2.me/theorems/d059e5bc-147b-4a58-bdc2-55446c8230dc
-- title:
--   fundamental vc compression with info: fundamental vc compression with info
-- statement:
--   The fundamental vc compression with info construction uses the fundamental vc compression with info property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Compression.lean#L1267-L1272
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Compression.lean#L1267-L1272

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

theorem fundamental_vc_compression_with_info
    (X : Type u) (C : ConceptClass X Bool) :
    (VCDim X C < ⊤) ↔
    (∃ (k : ℕ) (cs : CompressionSchemeWithInfo0 X Bool C), cs.size = k) := by sorry
