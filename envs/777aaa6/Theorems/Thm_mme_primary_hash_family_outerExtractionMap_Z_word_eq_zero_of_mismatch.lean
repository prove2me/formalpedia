-- Prove2me | Theorems.Thm_mme_primary_hash_family_outerExtractionMap_Z_word_eq_zero_of_mismatch
-- name    : mme_primary_hash_family_outerExtractionMap_Z_word_eq_zero_of_mismatch
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T12:52:12.001055+00:00
-- url     : https://prove2.me/theorems/2f140008-57b0-4b7c-80a6-098931b0be0c
-- title:
--   Shared-Z outer extraction vanishes on words missing every retained fiber
-- statement:
--   Consider a primary-hash family with $A$ outer fibers and its shared-third-mode outer extraction. Let a named third-mode basis word differ, for every outer fiber, from that fiber's retained shared address in at least one tensor-power coordinate. Then the complete outer extraction sends the basis word to zero. This is the generic projector-zeroing step that lets an extraction descend from a full tensor power to a source-faithful allowed-word subspace.
-- source:
--   Coppersmith--Winograd primary hashing and induced C-tensor extraction; projector form used in Duan--Wu--Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5.

import Definitions.Def_mme_coupled_Ctensor_outer_extraction_data
import Definitions.Def_mme_kron_pow_mode_word_basis

open MME MME.DWZComponentRestriction PiTensorProduct BigOperators Module
open CoupledCTensorPackaging

universe u

set_option autoImplicit false

theorem mme_primary_hash_family_outerExtractionMap_Z_word_eq_zero_of_mismatch
    {K : Type u} [Field K]
    {T : TensorObj K 3} (grading : T.TypeGrading 3)
    {N L G A H : ℕ}
    (family : CWQ6PrimaryHashFamily N L G A H)
    (hSupport : ∀ σ : Fin 3 → Fin 3,
      σ ≠ ![0, 0, 0] → σ ≠ ![1, 1, 1] →
      σ ≠ ![0, 1, 2] → σ ≠ ![1, 0, 2] →
      grading.blockTensor σ = 0)
    {ι : Type u} (b : Basis ι K (T.V 2)) (grade : ι → Fin 3)
    (hzero : ∀ (a : Fin 3) (j : ι), grade j ≠ a →
      grading.blockProj 2 a (b j) = 0)
    (w : PowIndex ι (2 * N))
    (hmismatch : ∀ a : Fin A, ∃ r : Fin (2 * N),
      grade (PowIndex.get (2 * N) w r) ≠
        componentAddress family a (firstFiberIndex family) 2 r) :
    outerExtractionMap grading family 2
        (kronPowModeBasis T 2 b (2 * N) w) = 0 := by
  sorry
