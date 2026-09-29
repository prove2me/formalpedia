-- Prove2me | solution 1 for mme_stothers_phi134_fine_block_restrict_outer_block
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-05T10:35:55.387968+00:00
-- url     : https://prove2.me/submissions/17a46e5c-1321-4cfe-86cf-ae56fb9cbafb

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi134_outer_grading
import Definitions.Def_mme_stothers_phi134_profile_data

open MME TensorProduct Module

universe u

namespace MME.StothersFourth.Phi134

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000

private theorem canonical_basis_mem_grade
    {K : Type u} [Field K]
    {V : Type u} [AddCommGroup V] [Module K V]
    {iota kappa : Type*} [DecidableEq kappa]
    (b : Basis iota K V) (g : iota → kappa) (i : iota) :
    b i ∈ cwBasisGrade b g (g i) := by
  exact Submodule.subset_span ⟨i, rfl, rfl⟩

private theorem square_basis_mem_own_grade
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3)
    (p : Fin (q + 2) × Fin (q + 2)) :
    cwSquareCanonicalBasis K q s p ∈
      (cwSquareCanonicalGrading K q).classOf s
        (cwSquarePairGrade q p) := by
  exact Submodule.subset_span ⟨p, rfl, rfl⟩

private theorem fourth_basis_apply
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3)
    (p : (Fin (q + 2) × Fin (q + 2)) ×
      (Fin (q + 2) × Fin (q + 2))) :
    cwFourthCanonicalBasis K q s p =
      cwSquareCanonicalBasis K q s p.1 ⊗ₜ[K]
        cwSquareCanonicalBasis K q s p.2 := by
  unfold cwFourthCanonicalBasis
  exact Module.Basis.tensorProduct_apply _ _ _ _

private theorem fourth_basis_mem_own_fine_grade
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3)
    (p : (Fin (q + 2) × Fin (q + 2)) ×
      (Fin (q + 2) × Fin (q + 2))) :
    cwFourthCanonicalBasis K q s p ∈
      (TensorObj.TypeGrading.kronGrading
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
  have hz := TensorObj.TypeGrading.classKronEmbed_mem
    G G s (cwSquarePairGrade q p.1) (cwSquarePairGrade q p.2) z
  change cwFourthCanonicalBasis K q s p ∈ _
  rw [fourth_basis_apply]
  simpa only [G, z, TensorObj.TypeGrading.classKronEmbed,
    TensorProduct.map_tmul, LinearMap.coe_restrictScalars,
    Submodule.coe_subtype, Subtype.coe_eta] using hz

private theorem fine_pair_mem_coarse
    (q : ℕ) (sx sy : Fin 3 → Fin 5)
    (hsum : ∀ s, (sx s).val + (sy s).val = (modeTotalGrade s).val)
    (s : Fin 3)
    (p : (Fin (q + 2) × Fin (q + 2)) ×
      (Fin (q + 2) × Fin (q + 2)))
    (hp : cwSquarePairGrade q p.1 = sx s ∧
      cwSquarePairGrade q p.2 = sy s) :
    cwFourthPairGrade q p = modeTotalGrade s := by
  apply Fin.ext
  simpa only [cwFourthPairGrade, hp.1, hp.2] using hsum s

/-- Inside the fixed coarse type `(1,3,4)`, remembering the first square
grade is equivalent to remembering the complete ordered pair of fine grades. -/
private theorem outerGrade_eq_iff_fine_pair
    (q : ℕ) (sx sy : Fin 3 → Fin 5)
    (hsum : ∀ s, (sx s).val + (sy s).val = (modeTotalGrade s).val)
    (s : Fin 3) (p : ModeIndex q s) :
    outerGrade q s p = sx s ↔
      cwSquarePairGrade q p.1.1 = sx s ∧
        cwSquarePairGrade q p.1.2 = sy s := by
  have hcoarse := congrArg Fin.val p.2
  constructor
  · intro hfirst
    have hx : cwSquarePairGrade q p.1.1 = sx s := by
      simpa only [outerGrade] using hfirst
    refine ⟨hx, ?_⟩
    apply Fin.ext
    have hxv := congrArg Fin.val hx
    have htotal := hsum s
    simp only [cwFourthPairGrade] at hcoarse
    omega
  · rintro ⟨hx, _⟩
    simpa only [outerGrade] using hx

private theorem outer_blockProj_basis
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3) (a : Fin 5)
    (p : ModeIndex q s) :
    (outerGrading K q).blockProj s a (canonicalBasis K q s p) =
      if h : outerGrade q s p = a then
        ⟨canonicalBasis K q s p, by
          simpa only [h] using canonical_basis_mem_grade
            (canonicalBasis K q s) (outerGrade q s) p⟩
      else 0 := by
  split_ifs with h
  · subst a
    exact TensorObj.TypeGrading.blockProj_apply_mem
      (outerGrading K q) s (outerGrade q s p) _
      (canonical_basis_mem_grade
        (canonicalBasis K q s) (outerGrade q s) p)
  · exact TensorObj.TypeGrading.blockProj_apply_mem_ne
      (outerGrading K q) s a (outerGrade q s p) (Ne.symm h) _
      (canonical_basis_mem_grade
        (canonicalBasis K q s) (outerGrade q s) p)

private theorem outer_class_le_fine_comap
    (K : Type u) [Field K] (q : ℕ)
    (sx sy : Fin 3 → Fin 5)
    (hsum : ∀ s, (sx s).val + (sy s).val = (modeTotalGrade s).val)
    (s : Fin 3) :
    (outerGrading K q).classOf s (sx s) ≤
      Submodule.comap
        ((cwFourthCanonicalGrading K q).classOf s
          (modeTotalGrade s)).subtype
        ((TensorObj.TypeGrading.kronGrading
          (cwSquareCanonicalGrading K q)
          (cwSquareCanonicalGrading K q)).classOf s
            (finProdFinEquiv (sx s, sy s))) := by
  change cwBasisGrade (canonicalBasis K q s)
      (outerGrade q s) (sx s) ≤ _
  unfold cwBasisGrade
  apply Submodule.span_le.2
  rintro _ ⟨p, hp, rfl⟩
  change (canonicalBasis K q s p).val ∈
    (TensorObj.TypeGrading.kronGrading
      (cwSquareCanonicalGrading K q)
      (cwSquareCanonicalGrading K q)).classOf s
        (finProdFinEquiv (sx s, sy s))
  rw [canonicalBasis_coe]
  have hm := fourth_basis_mem_own_fine_grade K q s p.1
  obtain ⟨hx, hy⟩ := (outerGrade_eq_iff_fine_pair q sx sy hsum s p).mp hp
  simpa only [hx, hy] using hm

/-- Canonical inclusion of one outer mode block into its literal fine block. -/
private noncomputable def outerClassToFine
    (K : Type u) [Field K] (q : ℕ)
    (sx sy : Fin 3 → Fin 5)
    (hsum : ∀ s, (sx s).val + (sy s).val = (modeTotalGrade s).val)
    (s : Fin 3) :
    (outerGrading K q).classOf s (sx s) →ₗ[K]
      (TensorObj.TypeGrading.kronGrading
        (cwSquareCanonicalGrading K q)
        (cwSquareCanonicalGrading K q)).classOf s
          (finProdFinEquiv (sx s, sy s)) :=
  LinearMap.codRestrict _
    (((cwFourthCanonicalGrading K q).classOf s
      (modeTotalGrade s)).subtype.comp
        ((outerGrading K q).classOf s (sx s)).subtype)
    (fun x => outer_class_le_fine_comap K q sx sy hsum s x.property)

@[simp] private theorem outerClassToFine_coe
    (K : Type u) [Field K] (q : ℕ)
    (sx sy : Fin 3 → Fin 5)
    (hsum : ∀ s, (sx s).val + (sy s).val = (modeTotalGrade s).val)
    (s : Fin 3) (x : (outerGrading K q).classOf s (sx s)) :
    (outerClassToFine K q sx sy hsum s x).val = x.1.1 := by
  rfl

private theorem coarse_blockProj_fourth_basis
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3)
    (p : (Fin (q + 2) × Fin (q + 2)) ×
      (Fin (q + 2) × Fin (q + 2))) :
    (cwFourthCanonicalGrading K q).blockProj s
        (modeTotalGrade s) (cwFourthCanonicalBasis K q s p) =
      if h : cwFourthPairGrade q p = modeTotalGrade s then
        canonicalBasis K q s ⟨p, h⟩
      else 0 := by
  split_ifs with h
  · rw [TensorObj.TypeGrading.blockProj_apply_mem]
    · apply Subtype.ext
      exact (canonicalBasis_coe K q s ⟨p, h⟩).symm
    · simpa only [h] using canonical_basis_mem_grade
        (cwFourthCanonicalBasis K q s) (cwFourthPairGrade q) p
  · exact TensorObj.TypeGrading.blockProj_apply_mem_ne
      (cwFourthCanonicalGrading K q) s (modeTotalGrade s)
      (cwFourthPairGrade q p) (Ne.symm h) _
      (canonical_basis_mem_grade
        (cwFourthCanonicalBasis K q s) (cwFourthPairGrade q) p)

private theorem fine_blockProj_fourth_basis
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3)
    (sx sy : Fin 3 → Fin 5)
    (p : (Fin (q + 2) × Fin (q + 2)) ×
      (Fin (q + 2) × Fin (q + 2))) :
    (TensorObj.TypeGrading.kronGrading
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
  let G := TensorObj.TypeGrading.kronGrading
    (cwSquareCanonicalGrading K q) (cwSquareCanonicalGrading K q)
  let own := finProdFinEquiv
    (cwSquarePairGrade q p.1, cwSquarePairGrade q p.2)
  have hp : cwFourthCanonicalBasis K q s p ∈ G.classOf s own :=
    fourth_basis_mem_own_fine_grade K q s p
  split_ifs with h
  · obtain ⟨hx, hy⟩ := h
    exact TensorObj.TypeGrading.blockProj_apply_mem G s
      (finProdFinEquiv (sx s, sy s)) _ (by
        simpa only [G, own, hx, hy] using hp)
  · have hne : finProdFinEquiv (sx s, sy s) ≠ own := by
      intro heq
      have hpair := finProdFinEquiv.injective heq
      apply h
      exact ⟨(congrArg Prod.fst hpair).symm,
        (congrArg Prod.snd hpair).symm⟩
    exact TensorObj.TypeGrading.blockProj_apply_mem_ne G s
      (finProdFinEquiv (sx s, sy s)) own hne _ hp

private theorem outerFine_projection_comp
    (K : Type u) [Field K] (q : ℕ)
    (sx sy : Fin 3 → Fin 5)
    (hsum : ∀ s, (sx s).val + (sy s).val = (modeTotalGrade s).val)
    (s : Fin 3) :
    (outerClassToFine K q sx sy hsum s).comp
        (((outerGrading K q).blockProj s (sx s)).comp
          ((cwFourthCanonicalGrading K q).blockProj s
            (modeTotalGrade s))) =
      (TensorObj.TypeGrading.kronGrading
        (cwSquareCanonicalGrading K q)
        (cwSquareCanonicalGrading K q)).blockProj s
          (finProdFinEquiv (sx s, sy s)) := by
  apply (cwFourthCanonicalBasis K q s).ext
  intro p
  simp only [LinearMap.comp_apply]
  by_cases hc : cwFourthPairGrade q p = modeTotalGrade s
  · have hcproj := coarse_blockProj_fourth_basis K q s p
    rw [dif_pos hc] at hcproj
    let pc : ModeIndex q s := ⟨p, hc⟩
    have hcstep := congrArg (fun x =>
      outerClassToFine K q sx sy hsum s
        ((outerGrading K q).blockProj s (sx s) x)) hcproj
    by_cases ho : outerGrade q s pc = sx s
    · have hoproj := outer_blockProj_basis K q s (sx s) pc
      rw [dif_pos ho] at hoproj
      have hfine := (outerGrade_eq_iff_fine_pair q sx sy hsum s pc).mp ho
      change cwSquarePairGrade q p.1 = sx s ∧
        cwSquarePairGrade q p.2 = sy s at hfine
      have hfproj := fine_blockProj_fourth_basis K q s sx sy p
      rw [dif_pos hfine] at hfproj
      calc
        _ = outerClassToFine K q sx sy hsum s
              ((outerGrading K q).blockProj s (sx s)
                (canonicalBasis K q s pc)) := hcstep
        _ = outerClassToFine K q sx sy hsum s
              ⟨canonicalBasis K q s pc, by
                simpa only [ho] using canonical_basis_mem_grade
                  (canonicalBasis K q s) (outerGrade q s) pc⟩ :=
            congrArg (outerClassToFine K q sx sy hsum s) hoproj
        _ = ⟨cwFourthCanonicalBasis K q s p, by
              simpa only [hfine.1, hfine.2] using
                fourth_basis_mem_own_fine_grade K q s p⟩ := by
            apply Subtype.ext
            exact canonicalBasis_coe K q s pc
        _ = _ := hfproj.symm
    · have hoproj := outer_blockProj_basis K q s (sx s) pc
      rw [dif_neg ho] at hoproj
      have hfine : ¬(cwSquarePairGrade q p.1 = sx s ∧
          cwSquarePairGrade q p.2 = sy s) := by
        intro hp
        exact ho ((outerGrade_eq_iff_fine_pair q sx sy hsum s pc).mpr hp)
      have hfproj := fine_blockProj_fourth_basis K q s sx sy p
      rw [dif_neg hfine] at hfproj
      calc
        _ = outerClassToFine K q sx sy hsum s
              ((outerGrading K q).blockProj s (sx s)
                (canonicalBasis K q s pc)) := hcstep
        _ = outerClassToFine K q sx sy hsum s 0 :=
          congrArg (outerClassToFine K q sx sy hsum s) hoproj
        _ = 0 := map_zero _
        _ = _ := hfproj.symm
  · have hcproj := coarse_blockProj_fourth_basis K q s p
    rw [dif_neg hc] at hcproj
    have hfine : ¬(cwSquarePairGrade q p.1 = sx s ∧
        cwSquarePairGrade q p.2 = sy s) := by
      intro hp
      exact hc (fine_pair_mem_coarse q sx sy hsum s p hp)
    have hfproj := fine_blockProj_fourth_basis K q s sx sy p
    rw [dif_neg hfine] at hfproj
    calc
      _ = outerClassToFine K q sx sy hsum s
            ((outerGrading K q).blockProj s (sx s) 0) :=
          congrArg (fun x =>
            outerClassToFine K q sx sy hsum s
              ((outerGrading K q).blockProj s (sx s) x)) hcproj
      _ = 0 := by simp only [map_zero]
      _ = _ := hfproj.symm

private theorem piTensorMap_three
    {K : Type u} [Field K]
    {d : ℕ} {V₀ V₁ V₂ V₃ : Fin d → Type u}
    [∀ i, AddCommGroup (V₀ i)] [∀ i, Module K (V₀ i)]
    [∀ i, AddCommGroup (V₁ i)] [∀ i, Module K (V₁ i)]
    [∀ i, AddCommGroup (V₂ i)] [∀ i, Module K (V₂ i)]
    [∀ i, AddCommGroup (V₃ i)] [∀ i, Module K (V₃ i)]
    (f : ∀ i, V₂ i →ₗ[K] V₃ i)
    (g : ∀ i, V₁ i →ₗ[K] V₂ i)
    (h : ∀ i, V₀ i →ₗ[K] V₁ i)
    (x : PiTensorProduct K V₀) :
    PiTensorProduct.map f
        (PiTensorProduct.map g (PiTensorProduct.map h x)) =
      PiTensorProduct.map
        (fun i => ((f i).comp (g i)).comp (h i)) x := by
  rw [← LinearMap.comp_apply, ← PiTensorProduct.map_comp]
  rw [← LinearMap.comp_apply, ← PiTensorProduct.map_comp]

/-- A literal fine block of `phi_134` is a restriction of the matching block
of the internal five-grading of the actual coarse constituent. -/
theorem fineBlock_restrict_outerBlock
    (K : Type u) [Field K] (q : ℕ)
    (sx sy : Fin 3 → Fin 5)
    (hsum : ∀ s, (sx s).val + (sy s).val = (modeTotalGrade s).val) :
    TensorObj.Restrict
      ((TensorObj.TypeGrading.kronGrading
        (cwSquareCanonicalGrading K q)
        (cwSquareCanonicalGrading K q)).blockSubtensor
          (fun s => finProdFinEquiv (sx s, sy s)))
      ((outerGrading K q).blockSubtensor sx) := by
  refine ⟨fun s => outerClassToFine K q sx sy hsum s, ?_⟩
  change PiTensorProduct.map
      (fun s => outerClassToFine K q sx sy hsum s)
      (PiTensorProduct.map
        (fun s => (outerGrading K q).blockProj s (sx s))
        (PiTensorProduct.map
          (fun s => (cwFourthCanonicalGrading K q).blockProj s
            (modeTotalGrade s))
          (cwFourthObj K q).t)) =
    PiTensorProduct.map
      (fun s =>
        (TensorObj.TypeGrading.kronGrading
          (cwSquareCanonicalGrading K q)
          (cwSquareCanonicalGrading K q)).blockProj s
            (finProdFinEquiv (sx s, sy s)))
      (cwFourthObj K q).t
  calc
    _ = PiTensorProduct.map (fun s =>
          ((outerClassToFine K q sx sy hsum s).comp
            ((outerGrading K q).blockProj s (sx s))).comp
              ((cwFourthCanonicalGrading K q).blockProj s
                (modeTotalGrade s))) (cwFourthObj K q).t :=
      piTensorMap_three
        (fun s => outerClassToFine K q sx sy hsum s)
        (fun s => (outerGrading K q).blockProj s (sx s))
        (fun s => (cwFourthCanonicalGrading K q).blockProj s
          (modeTotalGrade s)) (cwFourthObj K q).t
    _ = _ := by
      congr 1
      congr 1
      funext s
      apply LinearMap.ext
      intro x
      exact DFunLike.congr_fun
        (outerFine_projection_comp K q sx sy hsum s) x

end MME.StothersFourth.Phi134

open MME.StothersFourth.Phi134

set_option warningAsError true
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000

theorem solution
    {K : Type u} [Field K] (q : ℕ)
    (sx sy : Fin 3 → Fin 5)
    (hsum : ∀ s, (sx s).val + (sy s).val = (modeTotalGrade s).val) :
    TensorObj.Restrict
      ((TensorObj.TypeGrading.kronGrading
        (cwSquareCanonicalGrading K q)
        (cwSquareCanonicalGrading K q)).blockSubtensor
          (fun s => finProdFinEquiv (sx s, sy s)))
      ((outerGrading K q).blockSubtensor sx) :=
  fineBlock_restrict_outerBlock K q sx sy hsum
