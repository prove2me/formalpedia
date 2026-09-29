-- Prove2me | solution 1 for mme_CW_fourth_fine_block_restrict_coarse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T22:52:05.61981+00:00
-- url     : https://prove2.me/submissions/477e4b0a-7960-4adc-b335-b6e4ba9d8b32

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi116_fine_blocks

open MME TensorProduct Module
open MME.TensorObj.TypeGrading

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000

namespace MME.StothersFourth.Elementary

abbrev FourthIndex (q : ℕ) : Type :=
  (Fin (q + 2) × Fin (q + 2)) × (Fin (q + 2) × Fin (q + 2))

private theorem square_basis_mem_own_grade
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3)
    (p : Fin (q + 2) × Fin (q + 2)) :
    cwSquareCanonicalBasis K q s p ∈
      (cwSquareCanonicalGrading K q).classOf s
        (cwSquarePairGrade q p) := by
  exact Submodule.subset_span ⟨p, rfl, rfl⟩

private theorem fourth_basis_apply
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3)
    (p : FourthIndex q) :
    cwFourthCanonicalBasis K q s p =
      cwSquareCanonicalBasis K q s p.1 ⊗ₜ[K]
        cwSquareCanonicalBasis K q s p.2 := by
  unfold cwFourthCanonicalBasis
  exact Module.Basis.tensorProduct_apply _ _ _ _

private theorem fourth_basis_mem_own_fine_grade
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3)
    (p : FourthIndex q) :
    cwFourthCanonicalBasis K q s p ∈
      (kronGrading
        (cwSquareCanonicalGrading K q)
        (cwSquareCanonicalGrading K q)).classOf s
          (finProdFinEquiv
            (cwSquarePairGrade q p.1, cwSquarePairGrade q p.2)) := by
  let G := cwSquareCanonicalGrading K q
  let z : G.classOf s (cwSquarePairGrade q p.1) ⊗[K]
      G.classOf s (cwSquarePairGrade q p.2) :=
    ⟨cwSquareCanonicalBasis K q s p.1,
      square_basis_mem_own_grade K q s p.1⟩ ⊗ₜ[K]
    ⟨cwSquareCanonicalBasis K q s p.2,
      square_basis_mem_own_grade K q s p.2⟩
  have hz := classKronEmbed_mem G G s
    (cwSquarePairGrade q p.1) (cwSquarePairGrade q p.2) z
  change cwFourthCanonicalBasis K q s p ∈ _
  rw [fourth_basis_apply]
  simpa only [G, z, classKronEmbed, TensorProduct.map_tmul,
    LinearMap.coe_restrictScalars, Submodule.coe_subtype, Subtype.coe_eta]
    using hz

private theorem canonical_basis_mem_grade
    {K : Type u} [Field K]
    {V : Type u} [AddCommGroup V] [Module K V]
    {iota kappa : Type*} [DecidableEq kappa]
    (b : Basis iota K V) (g : iota → kappa) (i : iota) :
    b i ∈ cwBasisGrade b g (g i) := by
  exact Submodule.subset_span ⟨i, rfl, rfl⟩

private theorem fine_pair_mem_coarse
    (q : ℕ) (sx sy : Fin 3 → Fin 5) (sigma : Fin 3 → Fin 9)
    (hsum : ∀ s, (sx s).val + (sy s).val = (sigma s).val)
    (s : Fin 3) (p : FourthIndex q)
    (hp : cwSquarePairGrade q p.1 = sx s ∧
      cwSquarePairGrade q p.2 = sy s) :
    cwFourthPairGrade q p = sigma s := by
  apply Fin.ext
  simpa only [cwFourthPairGrade, hp.1, hp.2] using hsum s

private theorem coarse_blockProj_fourth_basis
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3)
    (sigma : Fin 3 → Fin 9) (p : FourthIndex q) :
    (cwFourthCanonicalGrading K q).blockProj s (sigma s)
        (cwFourthCanonicalBasis K q s p) =
      if h : cwFourthPairGrade q p = sigma s then
        ⟨cwFourthCanonicalBasis K q s p, by
          simpa only [h] using canonical_basis_mem_grade
            (cwFourthCanonicalBasis K q s) (cwFourthPairGrade q) p⟩
      else 0 := by
  split_ifs with h
  · exact blockProj_apply_mem
      (cwFourthCanonicalGrading K q) s (sigma s) _ (by
        simpa only [h] using canonical_basis_mem_grade
          (cwFourthCanonicalBasis K q s) (cwFourthPairGrade q) p)
  · exact blockProj_apply_mem_ne
      (cwFourthCanonicalGrading K q) s (sigma s)
      (cwFourthPairGrade q p) (Ne.symm h) _
      (canonical_basis_mem_grade
        (cwFourthCanonicalBasis K q s) (cwFourthPairGrade q) p)

private theorem fine_blockProj_fourth_basis
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3)
    (sx sy : Fin 3 → Fin 5) (p : FourthIndex q) :
    (kronGrading
      (cwSquareCanonicalGrading K q)
      (cwSquareCanonicalGrading K q)).blockProj s
        (finProdFinEquiv (sx s, sy s))
        (cwFourthCanonicalBasis K q s p) =
      if h : cwSquarePairGrade q p.1 = sx s ∧
          cwSquarePairGrade q p.2 = sy s then
        ⟨cwFourthCanonicalBasis K q s p, by
          obtain ⟨hx, hy⟩ := h
          simpa only [hx, hy] using
            fourth_basis_mem_own_fine_grade K q s p⟩
      else 0 := by
  let G := kronGrading
    (cwSquareCanonicalGrading K q) (cwSquareCanonicalGrading K q)
  let own := finProdFinEquiv
    (cwSquarePairGrade q p.1, cwSquarePairGrade q p.2)
  have hp : cwFourthCanonicalBasis K q s p ∈ G.classOf s own :=
    fourth_basis_mem_own_fine_grade K q s p
  split_ifs with h
  · obtain ⟨hx, hy⟩ := h
    exact blockProj_apply_mem G s (finProdFinEquiv (sx s, sy s)) _ (by
      simpa only [G, own, hx, hy] using hp)
  · have hne : finProdFinEquiv (sx s, sy s) ≠ own := by
      intro heq
      have hpair := finProdFinEquiv.injective heq
      apply h
      exact ⟨(congrArg Prod.fst hpair).symm,
        (congrArg Prod.snd hpair).symm⟩
    exact blockProj_apply_mem_ne G s
      (finProdFinEquiv (sx s, sy s)) own hne _ hp

private noncomputable def coarseToFine
    (K : Type u) [Field K] (q : ℕ)
    (sx sy : Fin 3 → Fin 5) (sigma : Fin 3 → Fin 9) (s : Fin 3) :
    (cwFourthCanonicalGrading K q).classOf s (sigma s) →ₗ[K]
      (kronGrading
        (cwSquareCanonicalGrading K q)
        (cwSquareCanonicalGrading K q)).classOf s
          (finProdFinEquiv (sx s, sy s)) :=
  ((kronGrading
    (cwSquareCanonicalGrading K q)
    (cwSquareCanonicalGrading K q)).blockProj s
      (finProdFinEquiv (sx s, sy s))).comp
        ((cwFourthCanonicalGrading K q).classOf s (sigma s)).subtype

private theorem coarseToFine_projection_comp
    (K : Type u) [Field K] (q : ℕ)
    (sx sy : Fin 3 → Fin 5) (sigma : Fin 3 → Fin 9)
    (hsum : ∀ s, (sx s).val + (sy s).val = (sigma s).val)
    (s : Fin 3) :
    (coarseToFine K q sx sy sigma s).comp
        ((cwFourthCanonicalGrading K q).blockProj s (sigma s)) =
      (kronGrading
        (cwSquareCanonicalGrading K q)
        (cwSquareCanonicalGrading K q)).blockProj s
          (finProdFinEquiv (sx s, sy s)) := by
  apply (cwFourthCanonicalBasis K q s).ext
  intro p
  simp only [LinearMap.comp_apply]
  by_cases hf : cwSquarePairGrade q p.1 = sx s ∧
      cwSquarePairGrade q p.2 = sy s
  · have hc := fine_pair_mem_coarse q sx sy sigma hsum s p hf
    rw [coarse_blockProj_fourth_basis K q s sigma p, dif_pos hc]
    unfold coarseToFine
    rfl
  · have hFine := fine_blockProj_fourth_basis K q s sx sy p
    rw [dif_neg hf] at hFine
    by_cases hc : cwFourthPairGrade q p = sigma s
    · rw [coarse_blockProj_fourth_basis K q s sigma p, dif_pos hc]
      unfold coarseToFine
      rfl
    · rw [coarse_blockProj_fourth_basis K q s sigma p, dif_neg hc]
      simp only [map_zero]
      exact hFine.symm

end MME.StothersFourth.Elementary

theorem solution
    {K : Type u} [Field K] (q : ℕ)
    (sx sy : Fin 3 → Fin 5) (sigma : Fin 3 → Fin 9)
    (hsum : ∀ s, (sx s).val + (sy s).val = (sigma s).val) :
    TensorObj.Restrict
      ((TensorObj.TypeGrading.kronGrading
        (cwSquareCanonicalGrading K q)
        (cwSquareCanonicalGrading K q)).blockSubtensor
          (fun s ↦ finProdFinEquiv (sx s, sy s)))
      ((MME.StothersFourth.cwFourthCanonicalGrading K q).blockSubtensor
        sigma) := by
  refine ⟨fun s ↦
    MME.StothersFourth.Elementary.coarseToFine K q sx sy sigma s, ?_⟩
  change PiTensorProduct.map
      (fun s ↦ MME.StothersFourth.Elementary.coarseToFine
        K q sx sy sigma s)
      (PiTensorProduct.map
        (fun s ↦ (MME.StothersFourth.cwFourthCanonicalGrading K q).blockProj
          s (sigma s))
        (MME.StothersFourth.cwFourthObj K q).t) =
    PiTensorProduct.map
      (fun s ↦ (TensorObj.TypeGrading.kronGrading
        (cwSquareCanonicalGrading K q)
        (cwSquareCanonicalGrading K q)).blockProj s
          (finProdFinEquiv (sx s, sy s)))
      (MME.StothersFourth.cwFourthObj K q).t
  rw [← LinearMap.comp_apply, ← PiTensorProduct.map_comp]
  have hmaps :
      (fun s ↦
        (MME.StothersFourth.Elementary.coarseToFine
          K q sx sy sigma s).comp
          ((MME.StothersFourth.cwFourthCanonicalGrading K q).blockProj
            s (sigma s))) =
      (fun s ↦ (TensorObj.TypeGrading.kronGrading
        (cwSquareCanonicalGrading K q)
        (cwSquareCanonicalGrading K q)).blockProj s
          (finProdFinEquiv (sx s, sy s))) := by
    funext s
    exact MME.StothersFourth.Elementary.coarseToFine_projection_comp
      K q sx sy sigma hsum s
  rw [hmaps]
  rfl
