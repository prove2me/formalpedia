-- Prove2me | solution 1 for mme_dwz_common_state_shared_tensor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-28T10:24:17.284005+00:00
-- url     : https://prove2.me/submissions/b0842ab6-f4ad-4967-8fdd-2a95fe65106a

import Theorems.Thm_mme_dwz_sourceWord_coarse_support_implies_xy_owner
import Theorems.Thm_mme_dwz_step1_filtered_broken_source_maps_preserve_tensor
import Theorems.Thm_mme_dwz_step1_filtered_source_family_restrict_of_xy_owner_and_singleton_cross_z_zero
import Theorems.Thm_mme_dwz_common_state_source_family_singleton_cross_zero

open MME Module PiTensorProduct

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000
set_option maxRecDepth 12000

open MME.DWZSourceAligned
open MME.DWZGlobalCorrelated

/-! Public-only four-child proof sketch for shared-tensor target `1ef54e59...`. -/

theorem solution
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
  intro m n p N L _hpPrime hpodd S hSrange hSfree A q reindex edge
    _hedgeInjective hBucket _hedgeProfile hXYOwner
  apply
    mme_dwz_step1_filtered_source_family_restrict_of_xy_owner_and_singleton_cross_z_zero
      (K := K) (m := m)
      (outer := sourceWord reindex edge)
      (copy := fun j ↦ commonStateBrokenCopy m reindex q edge j)
  · exact mme_dwz_sourceWord_coarse_support_implies_xy_owner
      reindex edge hXYOwner
  · intro j
    exact mme_dwz_step1_filtered_broken_source_maps_preserve_tensor
      (K := K) m (sourceWord reindex edge j)
        (commonStateBrokenCopy m reindex q edge j)
  · intro js h01 h02 W hSurvives
    exact mme_dwz_common_state_source_family_singleton_cross_zero
      (K := K) m reindex hpodd S hSrange hSfree A q edge hBucket
        js h01 h02 W hSurvives
