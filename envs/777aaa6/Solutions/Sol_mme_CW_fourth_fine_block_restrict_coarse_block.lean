-- Prove2me | solution 1 for mme_CW_fourth_fine_block_restrict_coarse_block
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:16:07.803621+00:00
-- url     : https://prove2.me/submissions/7e7e0ac7-8cf2-423c-accc-1f070d50b010

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi116_fine_blocks

open MME TensorProduct Module
open MME.TensorObj.TypeGrading
open MME.StothersFourth

universe uFine
set_option autoImplicit false

private theorem compatible_projection
    {K : Type uFine} [Field K] (q : Nat) (s : Fin 3)
    (a b : Fin 5) (c : Fin 9) (hsum : a.val + b.val = c.val) :
    ((kronGrading (cwSquareCanonicalGrading K q)
        (cwSquareCanonicalGrading K q)).blockProj s (finProdFinEquiv (a, b))).comp
      (((cwFourthCanonicalGrading K q).classOf s c).subtype.comp
        ((cwFourthCanonicalGrading K q).blockProj s c)) =
      (kronGrading (cwSquareCanonicalGrading K q)
        (cwSquareCanonicalGrading K q)).blockProj s (finProdFinEquiv (a, b)) := by
  classical
  apply (cwFourthCanonicalBasis K q s).ext
  intro p
  change ((kronGrading (cwSquareCanonicalGrading K q)
      (cwSquareCanonicalGrading K q)).blockProj s (finProdFinEquiv (a, b)))
      (((cwFourthCanonicalGrading K q).blockProj s c
        (cwFourthCanonicalBasis K q s p)) : (cwFourthObj K q).V s) = _
  have hp : cwFourthCanonicalBasis K q s p ∈
      (cwFourthCanonicalGrading K q).classOf s (cwFourthPairGrade q p) := by
    exact Submodule.subset_span (by exact ⟨p, rfl, rfl⟩)
  by_cases hc : c = cwFourthPairGrade q p
  · subst c
    rw [blockProj_apply_mem _ _ _ _ hp]
    rfl
  · rw [blockProj_apply_mem_ne _ _ _ _ hc _ hp]
    change ((kronGrading (cwSquareCanonicalGrading K q)
      (cwSquareCanonicalGrading K q)).blockProj s (finProdFinEquiv (a, b))) 0 = _
    rw [map_zero]
    rw [kronGrading_blockProj_eq]
    change 0 = classKronLift (cwSquareCanonicalGrading K q)
      (cwSquareCanonicalGrading K q) s a b
      (TensorProduct.map ((cwSquareCanonicalGrading K q).blockProj s a)
        ((cwSquareCanonicalGrading K q).blockProj s b)
        (cwFourthCanonicalBasis K q s p))
    have hbasis : cwFourthCanonicalBasis K q s p =
        cwSquareCanonicalBasis K q s p.1 ⊗ₜ[K]
          cwSquareCanonicalBasis K q s p.2 := by
      exact Basis.tensorProduct_apply' _ _ p
    rw [hbasis]
    erw [TensorProduct.map_tmul]
    have hp1 : cwSquareCanonicalBasis K q s p.1 ∈
        (cwSquareCanonicalGrading K q).classOf s (cwSquarePairGrade q p.1) := by
      exact Submodule.subset_span (by exact ⟨p.1, rfl, rfl⟩)
    have hp2 : cwSquareCanonicalBasis K q s p.2 ∈
        (cwSquareCanonicalGrading K q).classOf s (cwSquarePairGrade q p.2) := by
      exact Submodule.subset_span (by exact ⟨p.2, rfl, rfl⟩)
    by_cases ha : a = cwSquarePairGrade q p.1
    · have hb : b ≠ cwSquarePairGrade q p.2 := by
        intro hb
        apply hc
        apply Fin.ext
        simpa [cwFourthPairGrade, ha, hb] using hsum.symm
      rw [blockProj_apply_mem_ne _ _ _ _ hb _ hp2]
      simp
    · rw [blockProj_apply_mem_ne _ _ _ _ ha _ hp1]
      simp

theorem solution
    {K : Type uFine} [Field K] (q : Nat)
    (I₁ J₁ L₁ I₂ J₂ L₂ : Fin 5)
    (coarse : Fin 3 → Fin 9)
    (hsum : ∀ s,
      (cwSquareBlockType I₁ J₁ L₁ s).val +
          (cwSquareBlockType I₂ J₂ L₂ s).val =
        (coarse s).val) :
    TensorObj.Restrict
      (MME.StothersFourth.Phi116.cwFourthFineBlockObj
        K q I₁ J₁ L₁ I₂ J₂ L₂)
      ((MME.StothersFourth.cwFourthCanonicalGrading K q).blockSubtensor
        coarse) := by
  classical
  let fine := kronGrading (cwSquareCanonicalGrading K q)
    (cwSquareCanonicalGrading K q)
  let fineType := Phi116.cwFourthFineType I₁ J₁ L₁ I₂ J₂ L₂
  refine ⟨fun s => (fine.blockProj s (fineType s)).comp
    (((cwFourthCanonicalGrading K q).classOf s (coarse s)).subtype), ?_⟩
  change PiTensorProduct.map _
      (PiTensorProduct.map _ (cwFourthObj K q).t) =
    PiTensorProduct.map _ (cwFourthObj K q).t
  rw [← LinearMap.comp_apply]
  erw [← PiTensorProduct.map_comp]
  congr 1
  congr 1
  funext s
  exact compatible_projection q s _ _ _ (hsum s)
