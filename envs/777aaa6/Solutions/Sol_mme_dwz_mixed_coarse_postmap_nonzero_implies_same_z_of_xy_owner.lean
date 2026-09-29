-- Prove2me | solution 1 for mme_dwz_mixed_coarse_postmap_nonzero_implies_same_z_of_xy_owner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T20:21:16.929296+00:00
-- url     : https://prove2.me/submissions/f568d4fa-441f-42d1-acd4-2c52c29b817d

import Theorems.Thm_mme_gradedAddressProj_then_post_map_eq_zero_of_coordinate
import Theorems.Thm_mme_CW_square_canonical_support_and_scalar_blocks
import Definitions.Def_mme_dwz_source_aligned_broken_obj

open MME PiTensorProduct

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000
set_option maxRecDepth 10000

private theorem blockTensor_eq_zero_of_address_eq
    {K : Type u} [Field K] {T : TensorObj K 3} {t : ℕ}
    (G : T.TypeGrading t) {σ τ : Fin 3 → Fin t}
    (hστ : σ = τ) (hzero : G.blockTensor τ = 0) :
    G.blockTensor σ = 0 := by
  subst τ
  exact hzero

theorem solution
    {K : Type u} [Field K] {N k : ℕ}
    (outer : Fin k → Fin N → Fin 15)
    (js : Fin 3 → Fin k) (h01 : js 0 = js 1)
    {W : Fin 3 → Type u}
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (post : ∀ i : Fin 3,
      (gradedAddressBlock (cwSquareCanonicalGrading K 6)
        (fun i r ↦ MME.DWZSourceAligned.coarseAddress
          (outer (js i)) i r)).V i →ₗ[K] W i)
    (hNonzero :
      PiTensorProduct.map
          (fun i ↦ (post i).comp
            (gradedAddressProj (cwSquareCanonicalGrading K 6) N
              (fun i r ↦ MME.DWZSourceAligned.coarseAddress
                (outer (js i)) i r) i))
          ((TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow N).t ≠ 0) :
    ∀ r,
      MME.DWZSquare.shapeZ (outer (js 0) r) =
        MME.DWZSquare.shapeZ (outer (js 2) r) := by
  intro r
  let address : Fin 3 → Fin N → Fin 5 := fun i r ↦
    MME.DWZSourceAligned.coarseAddress (outer (js i)) i r
  have hBlock : (cwSquareCanonicalGrading K 6).blockTensor
      (fun i ↦ address i r) ≠ 0 := by
    intro hzero
    apply hNonzero
    exact mme_gradedAddressProj_then_post_map_eq_zero_of_coordinate
      (cwSquareCanonicalGrading K 6) address post r hzero
  let x := MME.DWZSquare.shapeX (outer (js 0) r)
  let y := MME.DWZSquare.shapeY (outer (js 1) r)
  let z := MME.DWZSquare.shapeZ (outer (js 2) r)
  have hAddress : (fun i ↦ address i r) = cwSquareBlockType x y z := by
    funext i
    fin_cases i <;> rfl
  have hMixedSum : x.val + y.val + z.val = 4 := by
    by_contra hsum
    have hzero :=
      (mme_CW_square_canonical_support_and_scalar_blocks (K := K) 6).1
        x y z hsum
    have hzeroMixed := blockTensor_eq_zero_of_address_eq
      (cwSquareCanonicalGrading K 6) hAddress hzero
    exact hBlock hzeroMixed
  rw [h01]
  apply Fin.ext
  dsimp only [x, y, z] at hMixedSum
  rw [h01] at hMixedSum
  have hOwn := MME.DWZSquare.shape_sum (outer (js 1) r)
  omega
