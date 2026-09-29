-- Prove2me | solution 1 for mme_recursive_profiled_CW_boundary_end
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-13T15:01:52.469855+00:00
-- url     : https://prove2.me/submissions/63a9bfff-8d20-4afb-bb03-e141673e7aa3

import Definitions.Def_mme_recursive_profiled_CW_data
import Theorems.Thm_mme_basis_projected_family_restrict
import Theorems.Thm_mme_recursive_yz_actual_cell_product_restriction
import Theorems.Thm_mme_recursive_yz_boundary_actual_matrix_extraction
import Theorems.Thm_mme_kronFin_MMObj_iso
import Definitions.Def_mme_kronFin_family_mode_map_basis_data

open MME MME.TensorObj MME.ProfiledCW MME.RecursiveYZ
  MME.RecursiveYZ.CWCells MME.CompleteSplit Module BigOperators
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

private theorem split_cast {S : Type} {ell L N : ℕ} (p : Fin L ≃ S)
    (h : L * 2 ^ (ell - 1) = N) (x : WordIndex.{u} 5 ell L) :
    split p h (fun j ↦ fine x (Fin.cast h.symm j)) = CWCells.label 5 ell L p x := by
  funext s r
  simp [split, CWCells.label, fine]

theorem solution {K : Type u} [Field K] {ell N : ℕ} {P : Predicate N}
    (B : BoundaryEnd ell N P) :
    Restrict (MMObj K B.a B.b B.c) (tensor K P) := by
  let parts := B.partition
  let child := parts.piece K 5 ell B.shape B.mu
  let a := fun j ↦ (B.profile j).a (B.zeroMode j)
  let b := fun j ↦ (B.profile j).b (B.zeroMode j)
  let c := fun j ↦ (B.profile j).c (B.zeroMode j)
  have hc (j) : Restrict (MMObj K (a j) (b j) (c j)) (child j) := by
    have heq : child j = (B.profile j).tensor K (B.zeroMode j) := by
      simp only [child, parts, Partition.piece, Boundary.Profile.tensor, B.shapes, B.profiles]
    rw [heq]
    exact mme_recursive_yz_boundary_actual_matrix_extraction (B.profile j) (B.zeroMode j)
  choose maps hm using hc
  have hprod : Restrict (kronFin parts.parts (fun j ↦ MMObj K (a j) (b j) (c j)))
      (kronFin parts.parts child) :=
    ⟨kronFinFamilyModeMap parts.parts child (fun j ↦ MMObj K (a j) (b j) (c j)) maps,
      kronFinFamilyModeMap_preserves_tensor child _ maps hm⟩
  have hboundary : Restrict (MMObj K B.a B.b B.c)
      (unbroken K 5 ell B.L (Equiv.refl _) B.cell B.shape B.mu) :=
    (mme_kronFin_MMObj_iso parts.parts a b c).2.trans
      (hprod.trans (mme_recursive_yz_actual_cell_product_restriction
        5 ell B.L (Equiv.refl _) B.cell B.shape B.mu parts))
  let pull : Predicate (B.L * 2 ^ (ell - 1)) :=
    fun i x ↦ P i (fun j ↦ x (Fin.cast B.length.symm j))
  have hmono : Restrict (unbroken K 5 ell B.L (Equiv.refl _) B.cell B.shape B.mu)
      (tensor K pull) := by
    apply mme_basis_projected_family_restrict (CWCells.source K 5 ell B.L)
      (CWCells.basis K 5 ell B.L) (fun i x ↦ pull i (fine x))
      (fun (_ : Fin 1) ↦ allowed 5 ell B.L (Equiv.refl _) B.cell B.shape B.mu)
    · intro j i x hx
      apply B.inside i (fun j ↦ fine x (Fin.cast B.length.symm j))
      rw [split_cast]
      exact hx
    · intro x js _ _
      exact ⟨0, funext (fun i ↦ Fin.eq_zero (js i))⟩
  have hp : tensor K pull = tensor K P := tensor_cast B.length P
  rw [hp] at hmono
  exact hboundary.trans hmono
