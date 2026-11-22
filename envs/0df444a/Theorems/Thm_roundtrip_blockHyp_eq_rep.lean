-- Prove2me | Theorems.Thm_roundtrip_blockHyp_eq_rep
-- name    : roundtrip_blockHyp_eq_rep
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:35:55.79488+00:00
-- url     : https://prove2.me/theorems/67c8c997-5ca6-437e-b7cc-28eda3ed1305
-- title:
--   roundtrip block Hyp eq rep: roundtrip block Hyp eq rep
-- statement:
--   Generic roundtrip theorem for the compression reconstruction invariant.
--
--   If:
--   * `encodeWitnessInfo` is used in `compressCore`,
--   * `decodeWitnessXCoords` and `decodeWitnessLabel` are used in `blockHyp`, and
--   * the kernel contains the witness pairs with the correct labels,
--
--   then the decoded block hypothesis is exactly the representative hypothesis.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Compression.lean#L458-L480
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Compression.lean#L458-L480

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

theorem roundtrip_blockHyp_eq_rep
    {X : Type u} [DecidableEq X]
    (learn : {m : ℕ} → (Fin m → X × Bool) → (X → Bool))
    (kernel : Finset (X × Bool)) (c : X → Bool) (K : ℕ)
    (W : Finset X) (h : X → Bool)
    (hK : kernel.card ≤ K)
    (hWker : ∀ x ∈ W, (x, c x) ∈ kernel)
    (hlabels : ∀ p ∈ kernel, p.2 = c p.1)
    (hrep : learn (labeledSampleOfFinset c W) = h)
    (x : X) :
    let info : Finset (Fin K) := encodeWitnessInfo kernel c K W
    let blockXCoords : Finset X := decodeWitnessXCoords kernel info
    let blockLabel : X → Bool := decodeWitnessLabel kernel
    learn (labeledSampleOfFinset blockLabel blockXCoords) x = h x := by sorry
