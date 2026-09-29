-- Prove2me | Theorems.Thm_mme_dwz_common_state_shared_tensor
-- name    : mme_dwz_common_state_shared_tensor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-28T09:40:22.941609+00:00
-- url     : https://prove2.me/theorems/1ef54e59-257a-4285-8ded-30d8fb7f3c99
-- title:
--   Common-state Step-1-filtered DWZ source tensor restriction
-- statement:
--   For any exact-profile owner enumeration contained in one canonical affine bucket, if supported mixed triples identify the X and Y owner, then the direct sum of the corresponding common-state broken address tensors is a restriction of the appropriate square Coppersmith--Winograd power. The affine state and all owner data are shared literally with the quantitative counting child.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 6, especially Claim 6.2, Claim 6.8, and Additional Zeroing-Out Steps 1 and 2; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_square_data
import Definitions.Def_mme_dwz_table2_integer_counts
import Definitions.Def_mme_dwz_source_aligned_broken_obj
import Definitions.Def_mme_dwz_global_common_state_broken_copy
import Definitions.Def_mme_CW_tensor

open MME

universe u

set_option autoImplicit false

/-!
# Universal common-state source tensor restriction

This is the tensor-only child of the raw Table-2 source theorem.  Its
statement deliberately exposes every hypothesis rather than hiding the
interface behind a newly published `Prop` definition.
-/

/-- The exact tensor restriction supplied by the paper-faithful Step-1 X/Y
filters and the correlated common-state Step-2 copies. -/

theorem mme_dwz_common_state_shared_tensor
    {K : Type u} [Field K] :
    ∀ {m n p N L : ℕ} [Fact p.Prime],
      Odd p →
      (S : Finset ℕ) →
      S ⊆ Finset.range (p / 2) →
      ThreeAPFree (S : Set ℕ) →
      (A : Finset (Fin (N + 1) → Fin 15)) →
      (q : (Fin (N + 2) → ZMod p) × ZMod p) →
      (reindex : Fin (N + 1) ≃ Fin L) →
      (edge : Fin n → Fin (N + 1) → Fin 15) →
      Function.Injective edge →
      (∀ r, edge r ∈ MME.dwzTable2AffineHashBucket S A q) →
      (∀ r s, Fintype.card
          {t : Fin L //
            MME.DWZGlobalCorrelated.sourceWord reindex edge r t = s} =
          MME.DWZTable2Counts.component s * m) →
      (∀ js : Fin 3 → Fin n,
        (∀ t : Fin (N + 1),
          (MME.DWZSquare.shapeX (edge (js 0) t)).val +
            (MME.DWZSquare.shapeY (edge (js 1) t)).val +
            (MME.DWZSquare.shapeZ (edge (js 2) t)).val = 4) →
        js 0 = js 1) →
      TensorObj.Restrict
        (TensorObj.bigAdd (fun r ↦
          MME.DWZSourceAligned.brokenAddressObj K m
            (MME.DWZGlobalCorrelated.sourceWord reindex edge r)
            (MME.DWZGlobalCorrelated.commonStateBrokenCopy
              m reindex q edge r)))
        ((TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow L) := by
  sorry
