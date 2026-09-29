-- Prove2me | solution 1 for mme_recursive_profiled_CW_exact_step
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-13T15:01:45.430987+00:00
-- url     : https://prove2.me/submissions/be14ac58-238d-44fd-9c96-fd3865f7c2a0

import Definitions.Def_mme_recursive_profiled_CW_data
import Theorems.Thm_mme_recursive_yz_profiled_repaired_CW_extraction

open MME MME.TensorObj MME.ProfiledCW MME.RecursiveYZ
  MME.RecursiveYZ.CWCells MME.CompleteSplit Module
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

private theorem flatten_label {S : Type} {ell L N : ℕ} (p : Fin L ≃ S)
    (h : L * 2 ^ (ell - 1) = N) (x : WordIndex.{u} 5 ell L) :
    flatten p h (CWCells.label 5 ell L p x) =
      fun j ↦ fine x (Fin.cast h.symm j) := by
  funext j
  simp only [flatten, CWCells.label, Equiv.symm_apply_apply, Prod.mk.eta,
    Equiv.apply_symm_apply, fine]

private theorem split_cast {S : Type} {ell L N : ℕ} (p : Fin L ≃ S)
    (h : L * 2 ^ (ell - 1) = N) (x : WordIndex.{u} 5 ell L) :
    split p h (fun j ↦ fine x (Fin.cast h.symm j)) = CWCells.label 5 ell L p x := by
  funext s r
  simp [split, CWCells.label, fine]

theorem solution {K : Type u} [Field K] {ell N : ℕ} {P : Predicate N}
    (E : ExactStep ell N P) :
    Restrict (bigAdd (fun _ : Fin E.copies ↦ tensor K E.output)) (tensor K P) := by
  let A := E.stage
  let D := E.hash
  have hs : (CWCells.source K 5 A.ell A.L).basisAllAllowedSubtensor
      (CWCells.basis K 5 A.ell A.L)
      (fun i x ↦ P i (flatten A.positions E.length (CWCells.label 5 A.ell A.L A.positions x))) =
      tensor K P := by
    calc
      _ = tensor K (fun i (x : FineWord (A.L * 2 ^ (A.ell - 1))) ↦
          P i (fun j ↦ x (Fin.cast E.length.symm j))) := by
        change (raw K _).basisAllAllowedSubtensor (canonical K _)
          (fun i x ↦ P i (flatten A.positions E.length (CWCells.label 5 A.ell A.L A.positions x))) = _
        unfold tensor
        congr 1
        funext i x
        rw [flatten_label]
      _ = _ := tensor_cast E.length P
  have ht : A.template K = tensor K E.output := by
    rw [← tensor_cast E.length E.output]
    change (raw K _).basisAllAllowedSubtensor (canonical K _)
      (allowed 5 A.ell A.L A.positions (fullCell A.total A.reference)
        (fun c i ↦ (c.2.val i).val) A.mu) = _
    unfold tensor
    congr 1
  have h := mme_recursive_yz_profiled_repaired_CW_extraction (K := K)
    5 A.ell D.half D.R D.N D.p A.L A.repairScale A.repairExponent E.count
    D.parent D.n A.total A.half_eq D.m D.positions A.positions
    (D.labels.image (fun a : ℕ ↦ (a : ZMod D.p))) E.state
    A.reference A.reference_target E.address E.injective E.target E.bucketed
    E.hashed E.isolated A.mu A.boundary (fun i j ↦ A.keep i (E.address j))
    (fun i f ↦ P i (flatten A.positions E.length f)) E.holes A.capacity
  change Restrict (bigAdd (fun _ : Fin E.copies ↦ A.template K)) _ at h
  rw [ht, hs] at h
  exact h
