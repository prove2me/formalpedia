-- Prove2me | Theorems.Thm_decodeWitnessLabel_eq_on_encoded
-- name    : decodeWitnessLabel_eq_on_encoded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:36:06.079845+00:00
-- url     : https://prove2.me/theorems/ff9080ca-70fb-45cc-bdcd-d80ce2fe7742
-- title:
--   decode Witness Label eq on encoded: decode Witness Label eq on encoded
-- statement:
--   On the encoded witness support, the decoded label function agrees with the true
--   label function `c`, provided every pair in the kernel has the correct second coordinate.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Compression.lean#L422-L437
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Compression.lean#L422-L437

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

theorem decodeWitnessLabel_eq_on_encoded
    {X : Type u} [DecidableEq X]
    (kernel : Finset (X × Bool)) (c : X → Bool) (W : Finset X)
    (hWker : ∀ x ∈ W, (x, c x) ∈ kernel)
    (hlabels : ∀ p ∈ kernel, p.2 = c p.1) :
    ∀ x ∈ W, decodeWitnessLabel kernel x = c x := by sorry
