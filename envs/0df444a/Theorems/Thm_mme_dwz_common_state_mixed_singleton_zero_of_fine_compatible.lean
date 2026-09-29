-- Prove2me | Theorems.Thm_mme_dwz_common_state_mixed_singleton_zero_of_fine_compatible
-- name    : mme_dwz_common_state_mixed_singleton_zero_of_fine_compatible
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T20:44:59.790177+00:00
-- url     : https://prove2.me/theorems/ce8258b2-f88d-40e7-a5da-5194038734a1
-- title:
--   Fine-compatible common-state singleton mixes vanish
-- statement:
--   Fix two distinct retained owners in one canonical affine state: a common X/Y owner and a Z owner. Let $W$ be a canonical Z-basis word retained by the Z owner's correlated broken copy. If hypothetical nonvanishing of the corresponding mixed singleton tensor would imply the exact retained fine-incidence condition for $W$ relative to the X/Y owner, then the mixed singleton tensor is zero. Coarse-Z agreement and the common-state affine hash equality are derived automatically, so the broken-copy uniqueness condition identifies the two owners, contradicting their assumed distinctness.

import Theorems.Thm_mme_dwz_common_state_ownerCompatible_of_mixed_postmap_nonzero
import Theorems.Thm_mme_dwz_common_state_surviving_word_value_eq_zero_of_competitor

open MME PiTensorProduct

universe u

set_option autoImplicit false

open MME.DWZSourceAligned
open MME.DWZGlobalCorrelated

theorem mme_dwz_common_state_mixed_singleton_zero_of_fine_compatible
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
    (js : Fin 3 → Fin n) (h01 : js 0 = js 1) (h02 : js 0 ≠ js 2)
    (W : AddressZWord (sourceWord reindex edge (js 2)))
    (hSurvives : addressWordSurvives m
      (sourceWord reindex edge (js 2))
      (commonStateBrokenCopy m reindex q edge (js 2)) W)
    {V : Fin 3 → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    (post : ∀ i : Fin 3,
      (gradedAddressBlock (cwSquareCanonicalGrading K 6)
        (fun i r ↦ coarseAddress
          (sourceWord reindex edge (js i)) i r)).V i →ₗ[K] V i)
    (hFine :
      let x := PiTensorProduct.map
        (fun i ↦ (post i).comp
          (gradedAddressProj (cwSquareCanonicalGrading K 6) L
            (fun i r ↦ coarseAddress
              (sourceWord reindex edge (js i)) i r) i))
        ((TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow L).t
      x ≠ 0 →
      ∀ hUseful : addressWordUseful m
          (sourceWord reindex edge (js 2)) W,
        MME.DWZStep2Source.retainedFineCompatible m
          (sourceWord reindex edge)
          (fun t ↦ MME.DWZStep1Support.fineSplitGrade
            ((addressUsefulBlock m
              (sourceWord reindex edge (js 2)) W hUseful).1 t).1
            ((addressUsefulBlock m
              (sourceWord reindex edge (js 2)) W hUseful).1 t).2)
          (js 0)) :
    PiTensorProduct.map
        (fun i ↦ (post i).comp
          (gradedAddressProj (cwSquareCanonicalGrading K 6) L
            (fun i r ↦ coarseAddress
              (sourceWord reindex edge (js i)) i r) i))
        ((TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow L).t = 0 := by
  sorry
