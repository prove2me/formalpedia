-- Prove2me | solution 1 for mme_recursive_yz_intact_template_MM_of_child_extractions
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-13T12:13:37.197978+00:00
-- url     : https://prove2.me/submissions/96129d86-3fa5-4676-a5a0-60c2e5845af4

import Definitions.Def_mme_recursive_yz_child_matrix_data
import Definitions.Def_mme_kronFin_family_mode_map_basis_data
import Definitions.Def_mme_tensor_quotient
import Theorems.Thm_mme_recursive_yz_actual_cell_product_restriction
import Theorems.Thm_mme_kronFin_MMObj_iso
open BigOperators MME MME.TensorObj MME.RecursiveYZ MME.RecursiveYZ.CWCells
  MME.RecursiveYZ.Certificate MME.CompleteSplit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1200000
universe u

private theorem full_cell_fiber {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    {n : Fin R → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (a : Address half R parent n) (r : Fin R)
    (c : MME.RecursiveThinSplit.Split half (parent r)) :
    Fintype.card {p : Position n // fullCell htotal a p = ⟨r,c⟩} =
      MME.RecursiveThinSplit.count (a r) c +
      MME.RecursiveThinSplit.count (a r) (complement (htotal r) c) := by
  classical
  let e : {p : Position n // fullCell htotal a p = ⟨r,c⟩} ≃
      {p : Fin (n r) × Fin 2 //
        (if p.2 = 0 then a r p.1 else complement (htotal r) (a r p.1)) = c} := {
    toFun := by
      rintro ⟨⟨r',t,h⟩,hp⟩
      have hr : r' = r := congrArg Sigma.fst hp
      subst r'
      exact ⟨(t,h), eq_of_heq (Sigma.mk.inj hp).2⟩
    invFun := fun p ↦ ⟨⟨r,p.val⟩, by
      change (⟨r,_⟩ : Cell half R parent) = ⟨r,c⟩
      rw [p.property]⟩
    left_inv := by
      rintro ⟨⟨r',t,h⟩,hp⟩
      have hr : r' = r := congrArg Sigma.fst hp
      subst r'
      rfl
    right_inv := by intro p; rfl }
  rw [Fintype.card_congr e, Fintype.card_subtype]
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_prod_type,
    Fin.sum_univ_two]
  have hc (t : Fin (n r)) : complement (htotal r) (a r t) = c ↔
      a r t = complement (htotal r) c := by
    constructor
    · intro h
      simpa only [complement_complement] using congrArg (complement (htotal r)) h
    · intro h
      rw [h, complement_complement]
  simp only [show (1 : Fin 2) ≠ 0 by decide, 
    MME.RecursiveThinSplit.count, Finset.card_eq_sum_ones, Finset.sum_filter,
    Finset.sum_add_distrib]
  simp only [ite_true, ite_false, hc]
  congr 1

theorem solution {K : Type u} [Field K] {D : HashExtraction.HashData}
    (A : Stage D) (M : A.ChildMM K) :
    Restrict (MMObj K M.dimA M.dimB M.dimC) (A.template K) := by
  classical
  have hcounts : ∀ r c, RecursiveThinSplit.count (A.reference r) c = D.m r c := by
    simpa only [RecursiveXHash.target, RecursiveThinSplit.HasJointCounts,
      Finset.mem_filter, Finset.mem_univ, true_and] using A.reference_target
  have hcard (j : Fin A.childCells) :
      Fintype.card {p : Position D.n // fullCell A.total A.reference p = A.childCell j} =
        A.childMultiplicity j := by
    simpa only [Stage.childMultiplicity, hcounts] using
      full_cell_fiber A.total A.reference (A.childCell j).1 (A.childCell j).2
  let part : Partition (fullCell A.total A.reference) := {
    parts := A.childCells
    cells := A.childCell
    size := A.childMultiplicity
    fiber := fun j ↦ (Fintype.equivFinOfCardEq (hcard j)).symm }
  have hfactor : Restrict (kronFin A.childCells (A.childTensor K)) (A.template K) :=
    mme_recursive_yz_actual_cell_product_restriction 5 A.ell A.L A.positions
      (fullCell A.total A.reference) (fun c i ↦ (c.2.val i).val) A.mu part
  choose f hf using M.extract
  have hlocal : Restrict
      (kronFin A.childCells (fun j ↦ MMObj K (M.a j) (M.b j) (M.c j)))
      (kronFin A.childCells (A.childTensor K)) :=
    ⟨kronFinFamilyModeMap A.childCells (A.childTensor K)
        (fun j ↦ MMObj K (M.a j) (M.b j) (M.c j)) f,
      kronFinFamilyModeMap_preserves_tensor _ _ f hf⟩
  exact (mme_kronFin_MMObj_iso A.childCells M.a M.b M.c).2.trans (hlocal.trans hfactor)
