-- Prove2me | solution 1 for mme_recursive_assembly_empty_iff
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T07:06:45.98132+00:00
-- url     : https://prove2.me/submissions/edd001a7-a09d-4404-b62f-a7fedb84f652

import Definitions.Def_mme_recursive_yz_stage_certificate
import Definitions.Def_mme_tensor_quotient
import Theorems.Thm_mme_MMObj_restrict_oneObj_iff
import Mathlib.Tactic

open MME MME.TensorObj MME.HashExtraction MME.RecursiveYZ.Certificate
open BigOperators
universe u
set_option autoImplicit false

namespace EmptyAssemblyCriterion

set_option backward.isDefEq.respectTransparency false in
lemma zero_restrict_unit {K : Type u} [Field K] :
    Restrict (zeroObj : TensorObj K 3) oneObj := by
  refine ⟨fun _ ↦ 0, ?_⟩
  dsimp only [zeroObj, oneObj]
  rw [PiTensorProduct.map_tprod]
  exact (PiTensorProduct.tprod K).map_coord_zero 0 rfl

end EmptyAssemblyCriterion

/-- With no factors and source power zero, repair either discards the sole empty-product
copy or leaves a matrix tensor that must have volume at most one. -/
theorem solution {K : Type u} [Field K]
    (D : Data) (A : ∀ j, Stage (D.hash j))
    (hfactors : D.factors = 0) (hpower : D.power = 0) :
    RecursiveAssembly D A K ↔ D.repairCopies ≠ 1 ∨ D.a * D.b * D.c ≤ 1 := by
  classical
  rcases D with ⟨factors, hash, repair, hrepair, a, b, c, power⟩
  dsimp only at hfactors hpower ⊢
  subst factors
  subst power
  have hr : Restrict (oneObj : TensorObj K 3) oneObj := Restrict.refl _
  by_cases h : repair = 1
  · subst repair
    simp only [RecursiveAssembly, kronFin, kronPow]
    simp only [Fin.prod_univ_zero, bigAdd]
    constructor
    · intro h
      exact Or.inr ((mme_MMObj_restrict_oneObj_iff a b c).mp
        (h.2 (fun j ↦ Fin.elim0 j) (fun j ↦ Fin.elim0 j)))
    · intro h
      refine ⟨hr, fun _ _ ↦ ?_⟩
      exact (mme_MMObj_restrict_oneObj_iff a b c).mpr (h.resolve_left (by simp))
  · have hdiv : 1 / repair = 0 := Nat.div_eq_of_lt (by omega)
    simp only [RecursiveAssembly, kronFin, kronPow]
    simp only [Fin.prod_univ_zero]
    constructor
    · exact fun _ ↦ Or.inl h
    · intro _
      refine ⟨hr, fun counts _ ↦ ?_⟩
      change Restrict (bigAdd (fun _ : Fin (1 / repair) ↦ MMObj K a b c)) oneObj
      rw [hdiv]
      exact EmptyAssemblyCriterion.zero_restrict_unit

#print axioms solution
