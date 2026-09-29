-- Prove2me | solution 1 for mme_global_CW_exact_stage_extraction
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-22T07:28:52.9998+00:00
-- url     : https://prove2.me/submissions/d4a5f090-76ca-44d3-ae9f-aaf5a5c6b0ff

import Definitions.Def_mme_global_CW_stage_data
import Theorems.Thm_mme_global_CW_repaired_extraction
import Theorems.Thm_mme_recursive_x_hash_finite_usable_isolation
import Theorems.Thm_mme_bigAdd_prefix_restrict
open BigOperators MME MME.TensorObj MME.ProfiledCW MME.CompleteSplit MME.GlobalCW
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
universe u

private theorem tensor_cast {K : Type u} [Field K] {n m : ℕ} (h : n = m)
    (P : Predicate m) :
    tensor K (fun i (x : FineWord n) ↦ P i (fun j ↦ x (Fin.cast h.symm j))) = tensor K P := by
  subst m
  rfl

theorem solution {K : Type u} [Field K] {ell M : ℕ}
    (D : ExactStage ell M) (hbudget : D.hash.Budget) :
    Restrict (bigAdd (fun _ : Fin D.copies ↦ tensor K D.output))
      (tensor K (fun _ (_ : FineWord M) ↦ True)) := by
  classical
  let H := D.hash
  letI : Fact H.p.Prime := ⟨H.prime⟩
  obtain ⟨state,I,hIT,hIE,hIg,hiso,hsize⟩ :=
    mme_recursive_x_hash_finite_usable_isolation H.half H.R H.parent H.n H.m H.odd H.grade_lt
      H.positions H.labels H.labels_range H.labels_free hbudget.1 H.good hbudget.2
  let enum : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let address : Fin (Fintype.card I) → H.Edge := fun j ↦ (enum j).val
  have hinj : Function.Injective address := Subtype.val_injective.comp enum.injective
  have hT j := hIT (enum j).property
  have hE j := hIE (enum j).property
  have hholes j i := D.good_holes state (address j) (hIg (enum j).property) i
  have hx := mme_global_CW_repaired_extraction (K := K) 5 ell H.half H.R H.N H.p
    D.L D.repairScale D.repairExponent (Fintype.card I) H.parent H.n D.degree_eq H.m
    H.positions D.positions (H.labels.image (fun a : ℕ ↦ (a : ZMod H.p))) state
    D.reference D.reference_target address hinj hT hE
    (fun j b hb he ↦ hiso (enum j).val (enum j).property b hb he) D.mu D.boundary hholes D.capacity
  have hs : (RecursiveYZ.CWCells.source K 5 ell D.L).basisAllAllowedSubtensor
      (RecursiveYZ.CWCells.basis K 5 ell D.L) (fun _ _ ↦ True) =
      tensor K (fun _ (_ : FineWord M) ↦ True) := by
    exact tensor_cast D.length (fun _ _ ↦ True)
  have ht : RecursiveYZ.CWCells.unbroken K 5 ell D.L D.positions (cell D.reference)
      (fun c i ↦ (c.2.val i).val) D.mu = tensor K D.output := by
    rw [← tensor_cast D.length D.output]
    change (raw K _).basisAllAllowedSubtensor (canonical K _)
      (RecursiveYZ.CWCells.allowed 5 ell D.L D.positions (cell D.reference)
        (fun c i ↦ (c.2.val i).val) D.mu) = _
    unfold tensor
    congr 1
  rw [hs,ht] at hx
  have hl : ⌈H.lower⌉₊ ≤ Fintype.card I := by
    apply Nat.ceil_le.mpr
    simpa only [Fintype.card_coe,HashExtraction.HashData.lower] using hsize
  have hc : D.copies ≤ Fintype.card I / 8 ^ D.repairExponent := Nat.div_le_div_right hl
  exact (mme_bigAdd_prefix_restrict (K := K) (by decide : 1 < 3) hc
    (fun _ ↦ tensor K D.output)).trans hx
