-- Prove2me | Theorems.Thm_decodeWitnessXCoords_encode_eq
-- name    : decodeWitnessXCoords_encode_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:35:54.60974+00:00
-- url     : https://prove2.me/theorems/60752ece-c061-49b0-ba44-e4ceef98c6fc
-- title:
--   decode Witness XCoords encode eq: decode Witness XCoords encode eq
-- statement:
--   If every `(x, c x)` with `x ∈ W` lies in `kernel`, and `kernel.card ≤ K`, then
--   decoding the encoded witness positions gives back exactly `W`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Compression.lean#L384-L418
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Compression.lean#L384-L418

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

theorem decodeWitnessXCoords_encode_eq
    {X : Type u} [DecidableEq X]
    (kernel : Finset (X × Bool)) (c : X → Bool) {K : ℕ}
    (W : Finset X)
    (hK : kernel.card ≤ K)
    (hWker : ∀ x ∈ W, (x, c x) ∈ kernel) :
    decodeWitnessXCoords kernel (encodeWitnessInfo kernel c K W) = W := by sorry
