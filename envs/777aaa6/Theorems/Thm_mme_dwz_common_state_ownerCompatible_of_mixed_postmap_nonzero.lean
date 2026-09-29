-- Prove2me | Theorems.Thm_mme_dwz_common_state_ownerCompatible_of_mixed_postmap_nonzero
-- name    : mme_dwz_common_state_ownerCompatible_of_mixed_postmap_nonzero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T20:34:56.163308+00:00
-- url     : https://prove2.me/theorems/f3a884ce-1258-4cc6-a98f-4f106eaa6f27
-- title:
--   Mixed coarse support and fine compatibility give common-state owner compatibility
-- statement:
--   Let a family of exact Table-2 component words lie in one canonical affine bucket at the common state $q$. Consider a mixed source block whose X and Y modes use one owner and whose Z mode uses another owner carrying a useful fine-Z word $z$. If this mixed block remains nonzero after arbitrary modewise postprocessing, and $z$ has the required retained fine-incidence profile relative to the X/Y owner, then that X/Y owner satisfies all three conditions in the common-state compatibility relation for $z$: it has the same complete coarse-Z word as the Z owner, it is fine-compatible with $z$, and it obeys the common-state X--Z hash equality. Thus the fine-incidence condition is the sole external combinatorial premise needed to invoke the correlated broken-copy uniqueness condition.

import Definitions.Def_mme_dwz_global_common_state_broken_copy
import Theorems.Thm_mme_dwz_mixed_coarse_postmap_nonzero_implies_same_z_of_xy_owner
import Theorems.Thm_mme_dwz_common_state_hash_retained_of_bucket_same_z

open MME PiTensorProduct

universe u

set_option autoImplicit false

open MME.DWZSourceAligned
open MME.DWZGlobalCorrelated

theorem mme_dwz_common_state_ownerCompatible_of_mixed_postmap_nonzero
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
  sorry
