-- Prove2me | solution 1 for mme_dwz_common_state_ownerCompatible_of_mixed_postmap_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T20:35:39.353631+00:00
-- url     : https://prove2.me/submissions/111a69e1-4a19-46a2-8b70-7de292728873

import Definitions.Def_mme_dwz_global_common_state_broken_copy
import Theorems.Thm_mme_dwz_mixed_coarse_postmap_nonzero_implies_same_z_of_xy_owner
import Theorems.Thm_mme_dwz_common_state_hash_retained_of_bucket_same_z

open MME PiTensorProduct

universe u

set_option autoImplicit false

open MME.DWZSourceAligned
open MME.DWZGlobalCorrelated

theorem solution
    {K : Type u} [Field K]
    (m : ℕ) {p N L n : ℕ}
    (reindex : Fin (N + 1) ≃ Fin L)
    (hpodd : Odd p)
    (S : Finset ℕ) (hSrange : S ⊆ Finset.range (p / 2))
    (hSfree : ThreeAPFree (S : Set ℕ))
    (A : Finset (Fin (N + 1) → Fin 15))
    (q : (Fin (N + 2) → ZMod p) × ZMod p)
    (edge : Fin n → Fin (N + 1) → Fin 15)
    (hBucket : ∀ j, edge j ∈ dwzTable2AffineHashBucket S A q)
    (js : Fin 3 → Fin n) (h01 : js 0 = js 1)
    (z : MME.DWZTable2StandardForm.UsefulBlock m
      (sourceWord reindex edge (js 2)))
    {V : Fin 3 → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    (post : ∀ i : Fin 3,
      (gradedAddressBlock (cwSquareCanonicalGrading K 6)
        (fun i r ↦ coarseAddress
          (sourceWord reindex edge (js i)) i r)).V i →ₗ[K] V i)
    (hNonzero :
      PiTensorProduct.map
          (fun i ↦ (post i).comp
            (gradedAddressProj (cwSquareCanonicalGrading K 6) L
              (fun i r ↦ coarseAddress
                (sourceWord reindex edge (js i)) i r) i))
          ((TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow L).t ≠ 0)
    (hFine : MME.DWZStep2Source.retainedFineCompatible m
      (sourceWord reindex edge)
      (fun t ↦ MME.DWZStep1Support.fineSplitGrade (z.1 t).1 (z.1 t).2)
      (js 0)) :
    ownerCompatible m reindex q edge (js 2) z (js 0) := by
  have hSourceZ :=
    mme_dwz_mixed_coarse_postmap_nonzero_implies_same_z_of_xy_owner
      (sourceWord reindex edge) js h01 post hNonzero
  have hSameZ : sameCoarseZ edge (js 2) (js 0) := by
    intro t
    have h := hSourceZ (reindex t)
    simpa only [sourceWord, Equiv.symm_apply_apply] using h
  refine ⟨hSameZ, hFine, ?_⟩
  exact mme_dwz_common_state_hash_retained_of_bucket_same_z
    hpodd S hSrange hSfree A q edge hBucket (js 2) (js 0) hSameZ
