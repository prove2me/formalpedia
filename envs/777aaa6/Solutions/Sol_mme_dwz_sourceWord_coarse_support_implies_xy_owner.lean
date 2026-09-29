-- Prove2me | solution 1 for mme_dwz_sourceWord_coarse_support_implies_xy_owner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-28T10:21:08.004462+00:00
-- url     : https://prove2.me/submissions/6d404abb-d6b3-4968-8b0a-bafaf0768f51

import Definitions.Def_mme_dwz_source_aligned_broken_obj
import Definitions.Def_mme_dwz_global_common_state_broken_copy
import Theorems.Thm_mme_CW_square_canonical_support_and_scalar_blocks

open MME

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000
set_option maxRecDepth 12000

open MME.DWZSourceAligned
open MME.DWZGlobalCorrelated

private theorem blockTensor_eq_zero_of_address_eq
    {K : Type u} [Field K] {T : TensorObj K 3} {t : ℕ}
    (G : T.TypeGrading t) {σ τ : Fin 3 → Fin t}
    (hστ : σ = τ) (hzero : G.blockTensor τ = 0) :
    G.blockTensor σ = 0 := by
  subst τ
  exact hzero

theorem solution
    {K : Type u} [Field K] {N L n : ℕ}
    (reindex : Fin (N + 1) ≃ Fin L)
    (edge : Fin n → Fin (N + 1) → Fin 15)
    (hXYOwner : ∀ js : Fin 3 → Fin n,
      (∀ t : Fin (N + 1),
        (MME.DWZSquare.shapeX (edge (js 0) t)).val +
          (MME.DWZSquare.shapeY (edge (js 1) t)).val +
          (MME.DWZSquare.shapeZ (edge (js 2) t)).val = 4) →
      js 0 = js 1) :
    ∀ js : Fin 3 → Fin n,
      (∀ r : Fin L,
        (cwSquareCanonicalGrading K 6).blockTensor
          (fun i ↦ coarseAddress
            (sourceWord reindex edge (js i)) i r) ≠ 0) →
      js 0 = js 1 := by
  intro js hSupported
  apply hXYOwner js
  intro t
  have hNonzero := hSupported (reindex t)
  by_contra hSum
  apply hNonzero
  have hZero :=
    (mme_CW_square_canonical_support_and_scalar_blocks (K := K) 6).1
      (MME.DWZSquare.shapeX (edge (js 0) t))
      (MME.DWZSquare.shapeY (edge (js 1) t))
      (MME.DWZSquare.shapeZ (edge (js 2) t)) hSum
  have hAddress :
      (fun i ↦ coarseAddress
        (sourceWord reindex edge (js i)) i (reindex t)) =
      cwSquareBlockType
        (MME.DWZSquare.shapeX (edge (js 0) t))
        (MME.DWZSquare.shapeY (edge (js 1) t))
        (MME.DWZSquare.shapeZ (edge (js 2) t)) := by
    funext i
    fin_cases i <;> simp [coarseAddress, sourceWord, cwSquareBlockType]
  exact blockTensor_eq_zero_of_address_eq
    (cwSquareCanonicalGrading K 6) hAddress hZero
