-- Prove2me | solution 1 for mme_stothers_phi116_outer_fine_block_restrictions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T19:34:10.58756+00:00
-- url     : https://prove2.me/submissions/6ad924c0-b371-4d04-94cf-8fd34d0d24eb

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi116_outer_grading
import Definitions.Def_mme_stothers_phi116_fine_blocks

open MME TensorProduct Module

universe u

namespace MME.StothersFourth.Phi116

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000

private theorem basis_mem_cwBasisGrade
    {K : Type u} [Field K]
    {V : Type u} [AddCommGroup V] [Module K V]
    {iota kappa : Type*} [DecidableEq kappa]
    (b : Basis iota K V) (g : iota → kappa) (i : iota) :
    b i ∈ cwBasisGrade b g (g i) := by
  exact Submodule.subset_span ⟨i, rfl, rfl⟩

theorem cwPhi116ThreeGrading_blockProj_basis
    (K : Type u) [Field K] (s : Fin 3) (a : Fin 3)
    (p : Phi116ModeIndex s) :
    (cwPhi116ThreeGrading K).blockProj s a
        (phi116CanonicalBasis K s p) =
      if h : phi116OuterGrade s p = a then
        ⟨phi116CanonicalBasis K s p, by
          simpa [h] using basis_mem_cwBasisGrade
            (phi116CanonicalBasis K s) (phi116OuterGrade s) p⟩
      else 0 := by
  split_ifs with h
  · subst a
    exact TensorObj.TypeGrading.blockProj_apply_mem
      (cwPhi116ThreeGrading K) s (phi116OuterGrade s p) _
      (basis_mem_cwBasisGrade
        (phi116CanonicalBasis K s) (phi116OuterGrade s) p)
  · exact TensorObj.TypeGrading.blockProj_apply_mem_ne
      (cwPhi116ThreeGrading K) s a (phi116OuterGrade s p) (Ne.symm h) _
      (basis_mem_cwBasisGrade
        (phi116CanonicalBasis K s) (phi116OuterGrade s) p)

end MME.StothersFourth.Phi116

open MME TensorProduct Module


namespace MME.StothersFourth.Phi116

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000

/-- The `012` outer block is exactly the fine block `013 ⊗ 103`. -/
theorem phi116_outer_grade_012_iff_fine_013_103
    (s : Fin 3) (p : Phi116ModeIndex s) :
    phi116OuterGrade s p = ![0, 1, 2] s ↔
      cwSquarePairGrade 6 p.1.1 = cwSquareBlockType 0 1 3 s ∧
      cwSquarePairGrade 6 p.1.2 = cwSquareBlockType 1 0 3 s := by
  have hsigma : ![0, 1, 2] s =
      match s with
      | ⟨0, _⟩ => (0 : Fin 3)
      | ⟨1, _⟩ => (1 : Fin 3)
      | ⟨2, _⟩ => (2 : Fin 3) := by
    fin_cases s <;> rfl
  conv_lhs =>
    rhs
    rw [hsigma]
  have hcoarse := congrArg Fin.val p.2
  fin_cases s <;>
    simp only [phi116OuterGrade, phi116OuterClass, phi116ModeTotalGrade,
      cwFourthBlockType, cwFourthPairGrade, cwSquareBlockType,
      Fin.isValue] at hcoarse ⊢ <;>
    split_ifs <;>
    simp only [Fin.ext_iff] at * <;>
    norm_num at * <;>
    omega

/-- The `102` outer block is exactly the fine block `103 ⊗ 013`. -/
theorem phi116_outer_grade_102_iff_fine_103_013
    (s : Fin 3) (p : Phi116ModeIndex s) :
    phi116OuterGrade s p = ![1, 0, 2] s ↔
      cwSquarePairGrade 6 p.1.1 = cwSquareBlockType 1 0 3 s ∧
      cwSquarePairGrade 6 p.1.2 = cwSquareBlockType 0 1 3 s := by
  have hsigma : ![1, 0, 2] s =
      match s with
      | ⟨0, _⟩ => (1 : Fin 3)
      | ⟨1, _⟩ => (0 : Fin 3)
      | ⟨2, _⟩ => (2 : Fin 3) := by
    fin_cases s <;> rfl
  conv_lhs =>
    rhs
    rw [hsigma]
  have hcoarse := congrArg Fin.val p.2
  fin_cases s <;>
    simp only [phi116OuterGrade, phi116OuterClass, phi116ModeTotalGrade,
      cwFourthBlockType, cwFourthPairGrade, cwSquareBlockType,
      Fin.isValue] at hcoarse ⊢ <;>
    split_ifs <;>
    simp only [Fin.ext_iff] at * <;>
    norm_num at * <;>
    omega

/-- The `000` outer block is exactly the fine block `004 ⊗ 112`. -/
theorem phi116_outer_grade_000_iff_fine_004_112
    (s : Fin 3) (p : Phi116ModeIndex s) :
    phi116OuterGrade s p = ![0, 0, 0] s ↔
      cwSquarePairGrade 6 p.1.1 = cwSquareBlockType 0 0 4 s ∧
      cwSquarePairGrade 6 p.1.2 = cwSquareBlockType 1 1 2 s := by
  have hsigma : ![0, 0, 0] s = (0 : Fin 3) := by
    fin_cases s <;> rfl
  conv_lhs =>
    rhs
    rw [hsigma]
  have hcoarse := congrArg Fin.val p.2
  fin_cases s <;>
    simp only [phi116OuterGrade, phi116OuterClass, phi116ModeTotalGrade,
      cwFourthBlockType, cwFourthPairGrade, cwSquareBlockType,
      Fin.isValue] at hcoarse ⊢ <;>
    split_ifs <;>
    simp only [Fin.ext_iff] at * <;>
    norm_num at * <;>
    omega

/-- The `111` outer block is exactly the fine block `112 ⊗ 004`. -/
theorem phi116_outer_grade_111_iff_fine_112_004
    (s : Fin 3) (p : Phi116ModeIndex s) :
    phi116OuterGrade s p = ![1, 1, 1] s ↔
      cwSquarePairGrade 6 p.1.1 = cwSquareBlockType 1 1 2 s ∧
      cwSquarePairGrade 6 p.1.2 = cwSquareBlockType 0 0 4 s := by
  have hsigma : ![1, 1, 1] s = (1 : Fin 3) := by
    fin_cases s <;> rfl
  conv_lhs =>
    rhs
    rw [hsigma]
  have hcoarse := congrArg Fin.val p.2
  fin_cases s <;>
    simp only [phi116OuterGrade, phi116OuterClass, phi116ModeTotalGrade,
      cwFourthBlockType, cwFourthPairGrade, cwSquareBlockType,
      Fin.isValue] at hcoarse ⊢ <;>
    split_ifs <;>
    simp only [Fin.ext_iff] at * <;>
    norm_num at * <;>
    omega

/-! ## Canonical-coordinate equivalences

These are the exact index-level identifications underlying the eventual
modewise linear equivalences of block subtensors.  In particular, they also
prove the converse direction: every coordinate of the named literal fine
block lies in the coarse `(1,1,6)` constituent.
-/

/-- Canonical coordinates selected by one block of the outer grading. -/
def Phi116OuterBlockIndex (sigma : Fin 3 → Fin 3) (s : Fin 3) : Type :=
  {p : Phi116ModeIndex s // phi116OuterGrade s p = sigma s}

/-- Canonical fourth-power coordinates selected by an ordered pair of square
block types. -/
def Phi116FineBlockIndex
    (sx sy : Fin 3 → Fin 5) (s : Fin 3) : Type :=
  {p : FourthIndex //
    cwSquarePairGrade 6 p.1 = sx s ∧
      cwSquarePairGrade 6 p.2 = sy s}

private theorem fine_pair_mem_phi116_coarse
    (sx sy : Fin 3 → Fin 5)
    (hsum : ∀ s, (sx s).val + (sy s).val =
      (phi116ModeTotalGrade s).val)
    (s : Fin 3) (p : FourthIndex)
    (hp : cwSquarePairGrade 6 p.1 = sx s ∧
      cwSquarePairGrade 6 p.2 = sy s) :
    cwFourthPairGrade 6 p = phi116ModeTotalGrade s := by
  apply Fin.ext
  simpa only [cwFourthPairGrade, hp.1, hp.2] using hsum s

/-- If an outer-grade predicate is equivalent to a literal fine-pair
predicate, their canonical coordinate types are equivalent by forgetting and
reconstructing the already-forced coarse membership proof. -/
def phi116OuterFineIndexEquiv
    (sigma : Fin 3 → Fin 3) (sx sy : Fin 3 → Fin 5)
    (hsum : ∀ s, (sx s).val + (sy s).val =
      (phi116ModeTotalGrade s).val)
    (hiff : ∀ (s : Fin 3) (p : Phi116ModeIndex s),
      phi116OuterGrade s p = sigma s ↔
        cwSquarePairGrade 6 p.1.1 = sx s ∧
          cwSquarePairGrade 6 p.1.2 = sy s)
    (s : Fin 3) :
    Phi116OuterBlockIndex sigma s ≃ Phi116FineBlockIndex sx sy s where
  toFun p := ⟨p.1.1, (hiff s p.1).mp p.2⟩
  invFun p :=
    let pc : Phi116ModeIndex s :=
      ⟨p.1, fine_pair_mem_phi116_coarse sx sy hsum s p.1 p.2⟩
    ⟨pc, (hiff s pc).mpr p.2⟩
  left_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv p := by
    apply Subtype.ext
    rfl

/-- Exact canonical-coordinate equivalence for `013 ⊗ 103`. -/
def phi116Outer012Fine013103Equiv (s : Fin 3) :
    Phi116OuterBlockIndex ![0, 1, 2] s ≃
      Phi116FineBlockIndex
        (cwSquareBlockType 0 1 3) (cwSquareBlockType 1 0 3) s :=
  phi116OuterFineIndexEquiv
    ![0, 1, 2] (cwSquareBlockType 0 1 3) (cwSquareBlockType 1 0 3)
    (by intro r; fin_cases r <;> rfl)
    phi116_outer_grade_012_iff_fine_013_103 s

/-- Exact canonical-coordinate equivalence for `103 ⊗ 013`. -/
def phi116Outer102Fine103013Equiv (s : Fin 3) :
    Phi116OuterBlockIndex ![1, 0, 2] s ≃
      Phi116FineBlockIndex
        (cwSquareBlockType 1 0 3) (cwSquareBlockType 0 1 3) s :=
  phi116OuterFineIndexEquiv
    ![1, 0, 2] (cwSquareBlockType 1 0 3) (cwSquareBlockType 0 1 3)
    (by intro r; fin_cases r <;> rfl)
    phi116_outer_grade_102_iff_fine_103_013 s

/-- Exact canonical-coordinate equivalence for `004 ⊗ 112`. -/
def phi116Outer000Fine004112Equiv (s : Fin 3) :
    Phi116OuterBlockIndex ![0, 0, 0] s ≃
      Phi116FineBlockIndex
        (cwSquareBlockType 0 0 4) (cwSquareBlockType 1 1 2) s :=
  phi116OuterFineIndexEquiv
    ![0, 0, 0] (cwSquareBlockType 0 0 4) (cwSquareBlockType 1 1 2)
    (by intro r; fin_cases r <;> rfl)
    phi116_outer_grade_000_iff_fine_004_112 s

/-- Exact canonical-coordinate equivalence for `112 ⊗ 004`. -/
def phi116Outer111Fine112004Equiv (s : Fin 3) :
    Phi116OuterBlockIndex ![1, 1, 1] s ≃
      Phi116FineBlockIndex
        (cwSquareBlockType 1 1 2) (cwSquareBlockType 0 0 4) s :=
  phi116OuterFineIndexEquiv
    ![1, 1, 1] (cwSquareBlockType 1 1 2) (cwSquareBlockType 0 0 4)
    (by intro r; fin_cases r <;> rfl)
    phi116_outer_grade_111_iff_fine_112_004 s

/-! ## Modewise block map

The product grading is built from collected bases, while the outer grading is
built from the literal fourth-power canonical basis.  The following two
lemmas bridge that representation difference without assuming that the bases
are definitionally equal.
-/

private theorem square_basis_mem_own_grade
    (K : Type u) [Field K] (s : Fin 3)
    (p : Fin 8 × Fin 8) :
    cwSquareCanonicalBasis K 6 s p ∈
      (cwSquareCanonicalGrading K 6).classOf s
        (cwSquarePairGrade 6 p) := by
  exact Submodule.subset_span ⟨p, rfl, rfl⟩

private theorem fourth_basis_apply
    (K : Type u) [Field K] (s : Fin 3) (p : FourthIndex) :
    cwFourthCanonicalBasis K 6 s p =
      cwSquareCanonicalBasis K 6 s p.1 ⊗ₜ[K]
        cwSquareCanonicalBasis K 6 s p.2 := by
  unfold cwFourthCanonicalBasis
  exact Module.Basis.tensorProduct_apply _ _ _ _

private theorem fourth_basis_mem_own_fine_grade
    (K : Type u) [Field K] (s : Fin 3) (p : FourthIndex) :
    cwFourthCanonicalBasis K 6 s p ∈
      (TensorObj.TypeGrading.kronGrading
        (cwSquareCanonicalGrading K 6)
        (cwSquareCanonicalGrading K 6)).classOf s
          (finProdFinEquiv
            (cwSquarePairGrade 6 p.1, cwSquarePairGrade 6 p.2)) := by
  let G := cwSquareCanonicalGrading K 6
  let z : G.classOf s (cwSquarePairGrade 6 p.1) ⊗[K]
      G.classOf s (cwSquarePairGrade 6 p.2) :=
    ⟨cwSquareCanonicalBasis K 6 s p.1,
      square_basis_mem_own_grade K s p.1⟩ ⊗ₜ[K]
    ⟨cwSquareCanonicalBasis K 6 s p.2,
      square_basis_mem_own_grade K s p.2⟩
  have hz := TensorObj.TypeGrading.classKronEmbed_mem
    G G s (cwSquarePairGrade 6 p.1) (cwSquarePairGrade 6 p.2) z
  change cwFourthCanonicalBasis K 6 s p ∈ _
  rw [fourth_basis_apply]
  simpa only [G, z, TensorObj.TypeGrading.classKronEmbed,
    TensorProduct.map_tmul, LinearMap.coe_restrictScalars,
    Submodule.coe_subtype, Subtype.coe_eta] using hz

private theorem phi116_outer_class_le_fine_comap
    (K : Type u) [Field K]
    (sigma : Fin 3 → Fin 3) (sx sy : Fin 3 → Fin 5)
    (hiff : ∀ (s : Fin 3) (p : Phi116ModeIndex s),
      phi116OuterGrade s p = sigma s ↔
        cwSquarePairGrade 6 p.1.1 = sx s ∧
          cwSquarePairGrade 6 p.1.2 = sy s)
    (s : Fin 3) :
    (cwPhi116ThreeGrading K).classOf s (sigma s) ≤
      Submodule.comap
        ((cwFourthCanonicalGrading K 6).classOf s
          (phi116ModeTotalGrade s)).subtype
        ((TensorObj.TypeGrading.kronGrading
          (cwSquareCanonicalGrading K 6)
          (cwSquareCanonicalGrading K 6)).classOf s
            (finProdFinEquiv (sx s, sy s))) := by
  change cwBasisGrade (phi116CanonicalBasis K s)
      (phi116OuterGrade s) (sigma s) ≤ _
  unfold cwBasisGrade
  apply Submodule.span_le.2
  rintro _ ⟨p, hp, rfl⟩
  change (phi116CanonicalBasis K s p).val ∈
    (TensorObj.TypeGrading.kronGrading
      (cwSquareCanonicalGrading K 6)
      (cwSquareCanonicalGrading K 6)).classOf s
        (finProdFinEquiv (sx s, sy s))
  rw [phi116CanonicalBasis_coe]
  have hm := fourth_basis_mem_own_fine_grade K s p.1
  obtain ⟨hx, hy⟩ := (hiff s p).mp hp
  simpa only [hx, hy] using hm

/-- Canonical inclusion of one outer `phi_116` mode block into the matching
literal fine product-grading mode block. -/
noncomputable def phi116OuterClassToFine
    (K : Type u) [Field K]
    (sigma : Fin 3 → Fin 3) (sx sy : Fin 3 → Fin 5)
    (hiff : ∀ (s : Fin 3) (p : Phi116ModeIndex s),
      phi116OuterGrade s p = sigma s ↔
        cwSquarePairGrade 6 p.1.1 = sx s ∧
          cwSquarePairGrade 6 p.1.2 = sy s)
    (s : Fin 3) :
    (cwPhi116ThreeGrading K).classOf s (sigma s) →ₗ[K]
      (TensorObj.TypeGrading.kronGrading
        (cwSquareCanonicalGrading K 6)
        (cwSquareCanonicalGrading K 6)).classOf s
          (finProdFinEquiv (sx s, sy s)) :=
  LinearMap.codRestrict _
    (((cwFourthCanonicalGrading K 6).classOf s
      (phi116ModeTotalGrade s)).subtype.comp
        ((cwPhi116ThreeGrading K).classOf s (sigma s)).subtype)
    (fun x => phi116_outer_class_le_fine_comap
      K sigma sx sy hiff s x.property)

@[simp] theorem phi116OuterClassToFine_coe
    (K : Type u) [Field K]
    (sigma : Fin 3 → Fin 3) (sx sy : Fin 3 → Fin 5)
    (hiff : ∀ (s : Fin 3) (p : Phi116ModeIndex s),
      phi116OuterGrade s p = sigma s ↔
        cwSquarePairGrade 6 p.1.1 = sx s ∧
          cwSquarePairGrade 6 p.1.2 = sy s)
    (s : Fin 3) (x : (cwPhi116ThreeGrading K).classOf s (sigma s)) :
    (phi116OuterClassToFine K sigma sx sy hiff s x).val = x.1.1 := by
  rfl

private theorem canonical_basis_mem_grade
    {K : Type u} [Field K]
    {V : Type u} [AddCommGroup V] [Module K V]
    {iota kappa : Type*} [DecidableEq kappa]
    (b : Basis iota K V) (g : iota → kappa) (i : iota) :
    b i ∈ cwBasisGrade b g (g i) := by
  exact Submodule.subset_span ⟨i, rfl, rfl⟩

private theorem coarse_blockProj_fourth_basis
    (K : Type u) [Field K] (s : Fin 3) (p : FourthIndex) :
    (cwFourthCanonicalGrading K 6).blockProj s
        (phi116ModeTotalGrade s) (cwFourthCanonicalBasis K 6 s p) =
      if h : cwFourthPairGrade 6 p = phi116ModeTotalGrade s then
        phi116CanonicalBasis K s ⟨p, h⟩
      else 0 := by
  split_ifs with h
  · rw [TensorObj.TypeGrading.blockProj_apply_mem]
    · apply Subtype.ext
      exact (phi116CanonicalBasis_coe K s ⟨p, h⟩).symm
    · simpa only [h] using canonical_basis_mem_grade
        (cwFourthCanonicalBasis K 6 s) (cwFourthPairGrade 6) p
  · exact TensorObj.TypeGrading.blockProj_apply_mem_ne
      (cwFourthCanonicalGrading K 6) s (phi116ModeTotalGrade s)
      (cwFourthPairGrade 6 p) (Ne.symm h) _
      (canonical_basis_mem_grade
        (cwFourthCanonicalBasis K 6 s) (cwFourthPairGrade 6) p)

private theorem fine_blockProj_fourth_basis
    (K : Type u) [Field K] (s : Fin 3) (sx sy : Fin 3 → Fin 5)
    (p : FourthIndex) :
    (TensorObj.TypeGrading.kronGrading
      (cwSquareCanonicalGrading K 6)
      (cwSquareCanonicalGrading K 6)).blockProj s
        (finProdFinEquiv (sx s, sy s))
        (cwFourthCanonicalBasis K 6 s p) =
      if h : cwSquarePairGrade 6 p.1 = sx s ∧
          cwSquarePairGrade 6 p.2 = sy s then
        ⟨cwFourthCanonicalBasis K 6 s p, by
          obtain ⟨hx, hy⟩ := h
          simpa only [hx, hy] using
            fourth_basis_mem_own_fine_grade K s p⟩
      else 0 := by
  let G := TensorObj.TypeGrading.kronGrading
    (cwSquareCanonicalGrading K 6) (cwSquareCanonicalGrading K 6)
  let own := finProdFinEquiv
    (cwSquarePairGrade 6 p.1, cwSquarePairGrade 6 p.2)
  have hp : cwFourthCanonicalBasis K 6 s p ∈ G.classOf s own := by
    exact fourth_basis_mem_own_fine_grade K s p
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

/-- Selecting a fine block directly from the fourth tensor agrees modewise
with first selecting the coarse `(1,1,6)` constituent, then its outer block,
and finally flattening the two nested subtypes. -/
theorem phi116_outerFine_projection_comp
    (K : Type u) [Field K]
    (sigma : Fin 3 → Fin 3) (sx sy : Fin 3 → Fin 5)
    (hsum : ∀ s, (sx s).val + (sy s).val =
      (phi116ModeTotalGrade s).val)
    (hiff : ∀ (s : Fin 3) (p : Phi116ModeIndex s),
      phi116OuterGrade s p = sigma s ↔
        cwSquarePairGrade 6 p.1.1 = sx s ∧
          cwSquarePairGrade 6 p.1.2 = sy s)
    (s : Fin 3) :
    (phi116OuterClassToFine K sigma sx sy hiff s).comp
        (((cwPhi116ThreeGrading K).blockProj s (sigma s)).comp
          ((cwFourthCanonicalGrading K 6).blockProj s
            (phi116ModeTotalGrade s))) =
      (TensorObj.TypeGrading.kronGrading
        (cwSquareCanonicalGrading K 6)
        (cwSquareCanonicalGrading K 6)).blockProj s
          (finProdFinEquiv (sx s, sy s)) := by
  apply (cwFourthCanonicalBasis K 6 s).ext
  intro (p : FourthIndex)
  simp only [LinearMap.comp_apply]
  by_cases hc : cwFourthPairGrade 6 p = phi116ModeTotalGrade s
  · have hcproj := coarse_blockProj_fourth_basis K s p
    rw [dif_pos hc] at hcproj
    let pc : Phi116ModeIndex s := ⟨p, hc⟩
    have hcstep := congrArg (fun x =>
      phi116OuterClassToFine K sigma sx sy hiff s
        ((cwPhi116ThreeGrading K).blockProj s (sigma s) x)) hcproj
    by_cases ho : phi116OuterGrade s pc = sigma s
    · have hoproj := cwPhi116ThreeGrading_blockProj_basis
        K s (sigma s) pc
      rw [dif_pos ho] at hoproj
      have hfine := (hiff s pc).mp ho
      change cwSquarePairGrade 6 p.1 = sx s ∧
        cwSquarePairGrade 6 p.2 = sy s at hfine
      have hfproj := fine_blockProj_fourth_basis K s sx sy p
      rw [dif_pos hfine] at hfproj
      calc
        _ = phi116OuterClassToFine K sigma sx sy hiff s
              ((cwPhi116ThreeGrading K).blockProj s (sigma s)
                (phi116CanonicalBasis K s pc)) := hcstep
        _ = phi116OuterClassToFine K sigma sx sy hiff s
              ⟨phi116CanonicalBasis K s pc, by
                simpa only [ho] using canonical_basis_mem_grade
                  (phi116CanonicalBasis K s) (phi116OuterGrade s) pc⟩ :=
            congrArg (phi116OuterClassToFine K sigma sx sy hiff s) hoproj
        _ = ⟨cwFourthCanonicalBasis K 6 s p, by
              simpa only [hfine.1, hfine.2] using
                fourth_basis_mem_own_fine_grade K s p⟩ := by
            apply Subtype.ext
            exact phi116CanonicalBasis_coe K s pc
        _ = _ := hfproj.symm
    · have hoproj := cwPhi116ThreeGrading_blockProj_basis
        K s (sigma s) pc
      rw [dif_neg ho] at hoproj
      have hfine : ¬(cwSquarePairGrade 6 p.1 = sx s ∧
          cwSquarePairGrade 6 p.2 = sy s) := by
        intro hp
        exact ho ((hiff s pc).mpr hp)
      have hfproj := fine_blockProj_fourth_basis K s sx sy p
      rw [dif_neg hfine] at hfproj
      calc
        _ = phi116OuterClassToFine K sigma sx sy hiff s
              ((cwPhi116ThreeGrading K).blockProj s (sigma s)
                (phi116CanonicalBasis K s pc)) := hcstep
        _ = phi116OuterClassToFine K sigma sx sy hiff s 0 :=
          congrArg (phi116OuterClassToFine K sigma sx sy hiff s) hoproj
        _ = 0 := map_zero _
        _ = _ := hfproj.symm
  · have hcproj := coarse_blockProj_fourth_basis K s p
    rw [dif_neg hc] at hcproj
    have hfine : ¬(cwSquarePairGrade 6 p.1 = sx s ∧
        cwSquarePairGrade 6 p.2 = sy s) := by
      intro hp
      exact hc (fine_pair_mem_phi116_coarse sx sy hsum s p hp)
    have hfproj := fine_blockProj_fourth_basis K s sx sy p
    rw [dif_neg hfine] at hfproj
    calc
      _ = phi116OuterClassToFine K sigma sx sy hiff s
            ((cwPhi116ThreeGrading K).blockProj s (sigma s) 0) :=
          congrArg (fun x =>
            phi116OuterClassToFine K sigma sx sy hiff s
              ((cwPhi116ThreeGrading K).blockProj s (sigma s) x)) hcproj
      _ = 0 := by simp only [map_zero]
      _ = _ := hfproj.symm

end MME.StothersFourth.Phi116
open MME TensorProduct Module


namespace MME.StothersFourth.Phi116

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000

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

/-- A literal fine product-grading block is a restriction of the matching
outer block.  The mode maps are canonical flattenings of nested subtypes. -/
theorem phi116_fineBlock_restrict_outerBlock
    (K : Type u) [Field K]
    (sigma : Fin 3 → Fin 3) (sx sy : Fin 3 → Fin 5)
    (hsum : ∀ s, (sx s).val + (sy s).val =
      (phi116ModeTotalGrade s).val)
    (hiff : ∀ (s : Fin 3) (p : Phi116ModeIndex s),
      phi116OuterGrade s p = sigma s ↔
        cwSquarePairGrade 6 p.1.1 = sx s ∧
          cwSquarePairGrade 6 p.1.2 = sy s) :
    TensorObj.Restrict
      ((TensorObj.TypeGrading.kronGrading
        (cwSquareCanonicalGrading K 6)
        (cwSquareCanonicalGrading K 6)).blockSubtensor
          (fun s => finProdFinEquiv (sx s, sy s)))
      ((cwPhi116ThreeGrading K).blockSubtensor sigma) := by
  refine ⟨fun s => phi116OuterClassToFine K sigma sx sy hiff s, ?_⟩
  change PiTensorProduct.map
      (fun s => phi116OuterClassToFine K sigma sx sy hiff s)
      (PiTensorProduct.map
        (fun s => (cwPhi116ThreeGrading K).blockProj s (sigma s))
        (PiTensorProduct.map
          (fun s => (cwFourthCanonicalGrading K 6).blockProj s
            (phi116ModeTotalGrade s))
          (cwFourthObj K 6).t)) =
    PiTensorProduct.map
      (fun s =>
        (TensorObj.TypeGrading.kronGrading
          (cwSquareCanonicalGrading K 6)
          (cwSquareCanonicalGrading K 6)).blockProj s
            (finProdFinEquiv (sx s, sy s)))
      (cwFourthObj K 6).t
  calc
    _ = PiTensorProduct.map (fun s =>
          ((phi116OuterClassToFine K sigma sx sy hiff s).comp
            ((cwPhi116ThreeGrading K).blockProj s (sigma s))).comp
              ((cwFourthCanonicalGrading K 6).blockProj s
                (phi116ModeTotalGrade s))) (cwFourthObj K 6).t :=
      piTensorMap_three
        (fun s => phi116OuterClassToFine K sigma sx sy hiff s)
        (fun s => (cwPhi116ThreeGrading K).blockProj s (sigma s))
        (fun s => (cwFourthCanonicalGrading K 6).blockProj s
          (phi116ModeTotalGrade s)) (cwFourthObj K 6).t
    _ = _ := by
      congr 1
      congr 1
      funext s
      apply LinearMap.ext
      intro x
      exact DFunLike.congr_fun
        (phi116_outerFine_projection_comp K sigma sx sy hsum hiff s) x

/-- The four literal fine blocks are restrictions of the four supported outer
blocks, in the source order `012`, `102`, `000`, `111`. -/
theorem cwPhi116_fine_blocks_restrict_outer_blocks
    (K : Type u) [Field K] :
    TensorObj.Restrict
      (cwFourthFineBlockObj K 6 0 1 3 1 0 3)
      ((cwPhi116ThreeGrading K).blockSubtensor ![0, 1, 2]) ∧
    TensorObj.Restrict
      (cwFourthFineBlockObj K 6 1 0 3 0 1 3)
      ((cwPhi116ThreeGrading K).blockSubtensor ![1, 0, 2]) ∧
    TensorObj.Restrict
      (cwFourthFineBlockObj K 6 0 0 4 1 1 2)
      ((cwPhi116ThreeGrading K).blockSubtensor ![0, 0, 0]) ∧
    TensorObj.Restrict
      (cwFourthFineBlockObj K 6 1 1 2 0 0 4)
      ((cwPhi116ThreeGrading K).blockSubtensor ![1, 1, 1]) := by
  constructor
  · simpa only [cwFourthFineBlockObj, cwFourthFineType] using
      phi116_fineBlock_restrict_outerBlock K
        ![0, 1, 2] (cwSquareBlockType 0 1 3)
        (cwSquareBlockType 1 0 3)
        (by intro s; fin_cases s <;> rfl)
        phi116_outer_grade_012_iff_fine_013_103
  constructor
  · simpa only [cwFourthFineBlockObj, cwFourthFineType] using
      phi116_fineBlock_restrict_outerBlock K
        ![1, 0, 2] (cwSquareBlockType 1 0 3)
        (cwSquareBlockType 0 1 3)
        (by intro s; fin_cases s <;> rfl)
        phi116_outer_grade_102_iff_fine_103_013
  constructor
  · simpa only [cwFourthFineBlockObj, cwFourthFineType] using
      phi116_fineBlock_restrict_outerBlock K
        ![0, 0, 0] (cwSquareBlockType 0 0 4)
        (cwSquareBlockType 1 1 2)
        (by intro s; fin_cases s <;> rfl)
        phi116_outer_grade_000_iff_fine_004_112
  · simpa only [cwFourthFineBlockObj, cwFourthFineType] using
      phi116_fineBlock_restrict_outerBlock K
        ![1, 1, 1] (cwSquareBlockType 1 1 2)
        (cwSquareBlockType 0 0 4)
        (by intro s; fin_cases s <;> rfl)
        phi116_outer_grade_111_iff_fine_112_004

end MME.StothersFourth.Phi116

theorem solution
    (K : Type u) [Field K] :
    TensorObj.Restrict
      (MME.StothersFourth.Phi116.cwFourthFineBlockObj K 6 0 1 3 1 0 3)
      ((MME.StothersFourth.Phi116.cwPhi116ThreeGrading K).blockSubtensor ![0, 1, 2]) ∧
    TensorObj.Restrict
      (MME.StothersFourth.Phi116.cwFourthFineBlockObj K 6 1 0 3 0 1 3)
      ((MME.StothersFourth.Phi116.cwPhi116ThreeGrading K).blockSubtensor ![1, 0, 2]) ∧
    TensorObj.Restrict
      (MME.StothersFourth.Phi116.cwFourthFineBlockObj K 6 0 0 4 1 1 2)
      ((MME.StothersFourth.Phi116.cwPhi116ThreeGrading K).blockSubtensor ![0, 0, 0]) ∧
    TensorObj.Restrict
      (MME.StothersFourth.Phi116.cwFourthFineBlockObj K 6 1 1 2 0 0 4)
      ((MME.StothersFourth.Phi116.cwPhi116ThreeGrading K).blockSubtensor ![1, 1, 1]) := by
  exact MME.StothersFourth.Phi116.cwPhi116_fine_blocks_restrict_outer_blocks K
