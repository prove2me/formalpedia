-- Prove2me | solution 1 for mme_primary_hash_family_sharedZ_Ctensor_star_assembly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T05:51:03.188136+00:00
-- url     : https://prove2.me/submissions/a2c65950-40be-42ab-8249-2f833b94a1ca

import Definitions.Def_CTensorOneHOneFamilyCertificate
import Definitions.Def_mme_CW_q6_primary_hash_family
import Definitions.Def_mme_induced_word_zeroing
import Definitions.Def_mme_TypeGrading_kron
import Theorems.Thm_mme_kronFin_MMObj_iso
import Theorems.Thm_mme_kronFin_respects_iso
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic

open MME PiTensorProduct BigOperators Module

universe u

set_option maxHeartbeats 800000


namespace CoupledCTensorPackaging

variable {K : Type u} [Field K]

def localM (q : ℕ) (sigma : Fin 3 → Fin 3) : ℕ :=
  if sigma 2 = 2 then q else 1

def localN (q : ℕ) (sigma : Fin 3 → Fin 3) : ℕ :=
  if sigma 2 = 2 then 1 else q

def localP (q : ℕ) (sigma : Fin 3 → Fin 3) : ℕ :=
  if sigma 2 = 2 then q else 1

private theorem supported_eq_one_of_four
    {sigma : Fin 3 → Fin 3}
    (hsigma :
      (sigma 0 = 0 ∧ sigma 1 = 0 ∧ sigma 2 = 0) ∨
      (sigma 0 = 1 ∧ sigma 1 = 1 ∧ sigma 2 = 1) ∨
      (sigma 0 = 0 ∧ sigma 1 = 1 ∧ sigma 2 = 2) ∨
      (sigma 0 = 1 ∧ sigma 1 = 0 ∧ sigma 2 = 2)) :
    sigma = ![0, 0, 0] ∨ sigma = ![1, 1, 1] ∨
      sigma = ![0, 1, 2] ∨ sigma = ![1, 0, 2] := by
  rcases hsigma with h | h | h | h
  · left
    funext i
    fin_cases i <;> simp_all
  · right; left
    funext i
    fin_cases i <;> simp_all
  · right; right; left
    funext i
    fin_cases i <;> simp_all
  · right; right; right
    funext i
    fin_cases i <;> simp_all

theorem supportedBlockIso
    {T : TensorObj K 3} (grading : T.TypeGrading 3)
    (q : ℕ)
    (h000 : TensorObj.Isomorphic (MMObj K 1 q 1)
      (grading.blockSubtensor ![0, 0, 0]))
    (h111 : TensorObj.Isomorphic (MMObj K 1 q 1)
      (grading.blockSubtensor ![1, 1, 1]))
    (h012 : TensorObj.Isomorphic (MMObj K q 1 q)
      (grading.blockSubtensor ![0, 1, 2]))
    (h102 : TensorObj.Isomorphic (MMObj K q 1 q)
      (grading.blockSubtensor ![1, 0, 2]))
    (sigma : Fin 3 → Fin 3)
    (hsigma :
      (sigma 0 = 0 ∧ sigma 1 = 0 ∧ sigma 2 = 0) ∨
      (sigma 0 = 1 ∧ sigma 1 = 1 ∧ sigma 2 = 1) ∨
      (sigma 0 = 0 ∧ sigma 1 = 1 ∧ sigma 2 = 2) ∨
      (sigma 0 = 1 ∧ sigma 1 = 0 ∧ sigma 2 = 2)) :
    TensorObj.Isomorphic
      (MMObj K (localM q sigma) (localN q sigma) (localP q sigma))
      (grading.blockSubtensor sigma) := by
  rcases supported_eq_one_of_four hsigma with h | h | h | h
  · subst sigma
    simpa [localM, localN, localP] using h000
  · subst sigma
    simpa [localM, localN, localP] using h111
  · subst sigma
    simpa [localM, localN, localP] using h012
  · subst sigma
    simpa [localM, localN, localP] using h102

theorem exactAddressBlockIso
    {T : TensorObj K 3} (grading : T.TypeGrading 3)
    (q N L G : ℕ)
    (h000 : TensorObj.Isomorphic (MMObj K 1 q 1)
      (grading.blockSubtensor ![0, 0, 0]))
    (h111 : TensorObj.Isomorphic (MMObj K 1 q 1)
      (grading.blockSubtensor ![1, 1, 1]))
    (h012 : TensorObj.Isomorphic (MMObj K q 1 q)
      (grading.blockSubtensor ![0, 1, 2]))
    (h102 : TensorObj.Isomorphic (MMObj K q 1 q)
      (grading.blockSubtensor ![1, 0, 2]))
    (address : CWQ6ExactCoupledAddress N L G) :
    TensorObj.Isomorphic
      (MMObj K
        (∏ j : Fin (2 * N), localM q (cwQ6CoupledAddressType address.1 j))
        (∏ j : Fin (2 * N), localN q (cwQ6CoupledAddressType address.1 j))
        (∏ j : Fin (2 * N), localP q (cwQ6CoupledAddressType address.1 j)))
      (gradedAddressBlock grading address.1) := by
  let M : Fin (2 * N) → TensorObj K 3 := fun j =>
    MMObj K
      (localM q (cwQ6CoupledAddressType address.1 j))
      (localN q (cwQ6CoupledAddressType address.1 j))
      (localP q (cwQ6CoupledAddressType address.1 j))
  let B : Fin (2 * N) → TensorObj K 3 := fun j =>
    grading.blockSubtensor (cwQ6CoupledAddressType address.1 j)
  have hpoint : ∀ j, TensorObj.Isomorphic (M j) (B j) := by
    intro j
    exact supportedBlockIso grading q h000 h111 h012 h102 _
      (address.2.1 j)
  have hfamily := mme_kronFin_respects_iso (2 * N) M B hpoint
  have hmm := mme_kronFin_MMObj_iso (K := K) (2 * N)
    (fun j => localM q (cwQ6CoupledAddressType address.1 j))
    (fun j => localN q (cwQ6CoupledAddressType address.1 j))
    (fun j => localP q (cwQ6CoupledAddressType address.1 j))
  exact hmm.symm.trans hfamily

private theorem prod_if_eq
    (q R : ℕ) (f : Fin R → Fin 3) (r : Fin 3) :
    (∏ j : Fin R, if f j = r then q else 1) =
      q ^ (Finset.univ.filter (fun j : Fin R => f j = r)).card := by
  classical
  rw [← Finset.prod_filter]
  simp

theorem exactAddressCommonVolume
    (q N L G : ℕ) (address : CWQ6ExactCoupledAddress N L G) :
    (∏ j : Fin (2 * N), localM q (cwQ6CoupledAddressType address.1 j)) *
      (∏ j : Fin (2 * N), localN q (cwQ6CoupledAddressType address.1 j)) *
      (∏ j : Fin (2 * N), localP q (cwQ6CoupledAddressType address.1 j)) =
        q ^ (4 * G + 2 * L) := by
  classical
  let zword : Fin (2 * N) → Fin 3 := fun j => address.1 2 j
  have hzcount (r : Fin 3) :
      (Finset.univ.filter (fun j : Fin (2 * N) => zword j = r)).card =
        cwQ6CoupledMarginalMultiplicity N L G 2 r := by
    exact address.2.2 2 r
  have hm :
      (∏ j : Fin (2 * N),
        localM q (cwQ6CoupledAddressType address.1 j)) = q ^ (2 * G) := by
    change (∏ j : Fin (2 * N), if zword j = 2 then q else 1) = _
    rw [prod_if_eq]
    rw [hzcount 2]
    simp [cwQ6CoupledMarginalMultiplicity]
  have hp :
      (∏ j : Fin (2 * N),
        localP q (cwQ6CoupledAddressType address.1 j)) = q ^ (2 * G) := by
    change (∏ j : Fin (2 * N), if zword j = 2 then q else 1) = _
    rw [prod_if_eq]
    rw [hzcount 2]
    simp [cwQ6CoupledMarginalMultiplicity]
  have hnpoint (j : Fin (2 * N)) :
      localN q (cwQ6CoupledAddressType address.1 j) =
        (if zword j = 0 then q else 1) *
          (if zword j = 1 then q else 1) := by
    change (if zword j = 2 then 1 else q) = _
    generalize hz : zword j = z
    fin_cases z <;> simp [hz]
  have hn :
      (∏ j : Fin (2 * N),
        localN q (cwQ6CoupledAddressType address.1 j)) = q ^ L * q ^ L := by
    simp_rw [hnpoint, Finset.prod_mul_distrib]
    rw [prod_if_eq, prod_if_eq, hzcount 0, hzcount 1]
    simp [cwQ6CoupledMarginalMultiplicity]
  rw [hm, hn, hp]
  simp only [← pow_add]
  congr 1
  omega

section SharedZStar

variable {T : TensorObj K 3} (grading : T.TypeGrading 3)
variable {q N L G A H : ℕ}

def firstFiberIndex (family : CWQ6PrimaryHashFamily N L G A H) : Fin H :=
  ⟨0, family.hHpos⟩

/-- Use the X/Y words of entry `(a,h)` and the fixed Z word of its outer
fiber.  This makes the shared third-mode space definitionally independent
of `h`. -/
def componentAddress
    (family : CWQ6PrimaryHashFamily N L G A H)
    (a : Fin A) (h : Fin H) : CWQ6CoupledAddress N :=
  cwQ6CoupledMixedAddress
    (family.entry (a, h)).1
    (family.entry (a, h)).1
    (family.entry (a, firstFiberIndex family)).1

theorem componentAddress_eq_entry
    (family : CWQ6PrimaryHashFamily N L G A H)
    (a : Fin A) (h : Fin H) :
    componentAddress family a h = (family.entry (a, h)).1 := by
  funext i j
  fin_cases i
  · rfl
  · rfl
  · exact congrFun
      (family.zSameFiber a (firstFiberIndex family) h) j

def componentExactAddress
    (family : CWQ6PrimaryHashFamily N L G A H)
    (a : Fin A) (h : Fin H) : CWQ6ExactCoupledAddress N L G :=
  ⟨componentAddress family a h, by
    rw [componentAddress_eq_entry]
    exact (family.entry (a, h)).2⟩

noncomputable def componentObj
    (family : CWQ6PrimaryHashFamily N L G A H)
    (a : Fin A) (h : Fin H) : TensorObj K 3 :=
  gradedAddressBlock grading (componentAddress family a h)

noncomputable def gradedAddressBlockModeEquiv
    {t : ℕ} {X : TensorObj K 3} (G0 : X.TypeGrading t) :
    (R : ℕ) → (address address' : Fin 3 → Fin R → Fin t) →
      (i : Fin 3) → (address i = address' i) →
      (gradedAddressBlock G0 address).V i ≃ₗ[K]
        (gradedAddressBlock G0 address').V i
  | 0, _, _, _, _ => LinearEquiv.refl K K
  | R + 1, address, address', i, hi =>
      TensorProduct.congr
        (LinearEquiv.ofEq
          (G0.classOf i (address i 0))
          (G0.classOf i (address' i 0))
          (by rw [congrFun hi 0]))
        (gradedAddressBlockModeEquiv G0 R
          (fun i' j => address i' j.succ)
          (fun i' j => address' i' j.succ) i (by
            funext j
            exact congrFun hi j.succ))

noncomputable def componentZEquiv
    (family : CWQ6PrimaryHashFamily N L G A H)
    (a : Fin A) (h : Fin H) :
    (componentObj grading family a h).V 2 ≃ₗ[K]
      (componentObj grading family a (firstFiberIndex family)).V 2 := by
  exact gradedAddressBlockModeEquiv grading (2 * N)
    (componentAddress family a h)
    (componentAddress family a (firstFiberIndex family)) 2 (by rfl)

@[reducible] def starSpace
    (family : CWQ6PrimaryHashFamily N L G A H)
    (a : Fin A) : Fin 3 → Type u
  | 0 => ∀ h : Fin H, (componentObj grading family a h).V 0
  | 1 => ∀ h : Fin H, (componentObj grading family a h).V 1
  | 2 => (componentObj grading family a (firstFiberIndex family)).V 2

noncomputable instance starSpaceAddCommGroup
    (family : CWQ6PrimaryHashFamily N L G A H)
    (a : Fin A) (i : Fin 3) :
    AddCommGroup (starSpace grading family a i) :=
  match i with
  | 0 => Pi.addCommGroup
  | 1 => Pi.addCommGroup
  | 2 =>
      (componentObj grading family a (firstFiberIndex family)).acg 2

noncomputable instance starSpaceModule
    (family : CWQ6PrimaryHashFamily N L G A H)
    (a : Fin A) (i : Fin 3) :
    Module K (starSpace grading family a i) :=
  match i with
  | 0 => Pi.module _ _ _
  | 1 => Pi.module _ _ _
  | 2 =>
      (componentObj grading family a (firstFiberIndex family)).mod 2

instance starSpaceFinite
    (family : CWQ6PrimaryHashFamily N L G A H)
    (a : Fin A) (i : Fin 3) :
    Module.Finite K (starSpace grading family a i) :=
  match i with
  | 0 => inferInstanceAs
      (Module.Finite K
        (∀ h : Fin H, (componentObj grading family a h).V 0))
  | 1 => inferInstanceAs
      (Module.Finite K
        (∀ h : Fin H, (componentObj grading family a h).V 1))
  | 2 =>
      (componentObj grading family a (firstFiberIndex family)).fin 2

/-- Include a graded address block back into its ambient tensor power. -/
noncomputable def gradedAddressEmbed
    {t : ℕ} {X : TensorObj K 3} (G0 : X.TypeGrading t) :
    (R : ℕ) → (address : Fin 3 → Fin R → Fin t) → (i : Fin 3) →
      (gradedAddressBlock G0 address).V i →ₗ[K] (X.kronPow R).V i
  | 0, _, _ => LinearMap.id
  | R + 1, address, i =>
      TensorProduct.map
        (G0.classOf i (address i 0)).subtype
        (gradedAddressEmbed G0 R (fun i' j => address i' j.succ) i)

noncomputable def componentInclusion
    (family : CWQ6PrimaryHashFamily N L G A H)
    (a : Fin A) (h : Fin H) : ∀ i : Fin 3,
    (componentObj grading family a h).V i →ₗ[K]
      starSpace grading family a i
  | 0 => LinearMap.single K
      (fun k : Fin H => (componentObj grading family a k).V 0) h
  | 1 => LinearMap.single K
      (fun k : Fin H => (componentObj grading family a k).V 1) h
  | 2 => (componentZEquiv grading family a h).toLinearMap

noncomputable def starObj
    (family : CWQ6PrimaryHashFamily N L G A H)
    (a : Fin A) : TensorObj K 3 where
  V := starSpace grading family a
  t := ∑ h : Fin H,
    PiTensorProduct.map (componentInclusion grading family a h)
      (componentObj grading family a h).t

@[reducible] def starBasisIndex
    (family : CWQ6PrimaryHashFamily N L G A H)
    (a : Fin A) : Fin 3 → Type
  | 0 => Σ h : Fin H,
      Fin (Module.finrank K ((componentObj grading family a h).V 0))
  | 1 => Σ h : Fin H,
      Fin (Module.finrank K ((componentObj grading family a h).V 1))
  | 2 => Fin (Module.finrank K
      ((componentObj grading family a (firstFiberIndex family)).V 2))

private instance starBasisIndexFinite
    (family : CWQ6PrimaryHashFamily N L G A H)
    (a : Fin A) (i : Fin 3) :
    Finite (starBasisIndex grading family a i) := by
  exact match i with
  | 0 => inferInstance
  | 1 => inferInstance
  | 2 => inferInstance

private noncomputable instance starBasisIndexDecidableEq
    (family : CWQ6PrimaryHashFamily N L G A H)
    (a : Fin A) (i : Fin 3) :
    DecidableEq (starBasisIndex grading family a i) := by
  exact match i with
  | 0 => inferInstance
  | 1 => inferInstance
  | 2 => inferInstance

noncomputable def starBasis
    (family : CWQ6PrimaryHashFamily N L G A H)
    (a : Fin A) (i : Fin 3) :
    Basis (starBasisIndex grading family a i) K
      ((starObj grading family a).V i) := by
  exact match i with
  | 0 => Pi.basis (fun h =>
      Module.finBasis K ((componentObj grading family a h).V 0))
  | 1 => Pi.basis (fun h =>
      Module.finBasis K ((componentObj grading family a h).V 1))
  | 2 => Module.finBasis K
      ((componentObj grading family a (firstFiberIndex family)).V 2)

def starBasisGrade
    (family : CWQ6PrimaryHashFamily N L G A H)
    (a : Fin A) : ∀ i : Fin 3,
      starBasisIndex grading family a i → Fin (H + 1)
  | 0, j => Fin.castSucc j.1
  | 1, j => Fin.castSucc j.1
  | 2, _ => Fin.last H

noncomputable def starGrading
    (family : CWQ6PrimaryHashFamily N L G A H)
    (a : Fin A) : (starObj grading family a).TypeGrading (H + 1) where
  decomp i := cwBasisGrade (starBasis grading family a i)
    (starBasisGrade grading family a i)
  is_internal i := cwBasisGrade_isInternal
    (starBasis grading family a i)
    (starBasisGrade grading family a i)

private theorem basisGrade_mem_of_const
    {V : Type u} [AddCommGroup V] [Module K V]
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ]
    (b : Basis ι K V) (a : κ) (x : V) :
    x ∈ cwBasisGrade b (fun _ => a) a := by
  classical
  rw [← b.sum_repr x]
  apply Submodule.sum_mem
  intro j hj
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨j, by simp, rfl⟩

theorem componentInclusion_mem
    (family : CWQ6PrimaryHashFamily N L G A H)
    (a : Fin A) (h : Fin H) (i : Fin 3)
    (x : (componentObj grading family a h).V i) :
    componentInclusion grading family a h i x ∈
      (starGrading grading family a).classOf i
        (cTensorOneHOneAddress H h i) := by
  classical
  fin_cases i
  · letI : Module K
        (∀ k : Fin H, (componentObj grading family a k).V 0) :=
      Pi.module _ _ _
    change (LinearMap.single K
      (fun k : Fin H => (componentObj grading family a k).V 0) h) x ∈ _
    rw [← (Module.finBasis K
      ((componentObj grading family a h).V 0)).sum_repr x]
    rw [map_sum]
    simp only [map_smul]
    apply Submodule.sum_mem
    intro j hj
    apply Submodule.smul_mem
    change (LinearMap.single K
      (fun k : Fin H => (componentObj grading family a k).V 0) h)
        ((Module.finBasis K
          ((componentObj grading family a h).V 0)) j) ∈
      cwBasisGrade (starBasis grading family a 0)
        (starBasisGrade grading family a 0) (Fin.castSucc h)
    unfold cwBasisGrade
    apply Submodule.subset_span
    refine ⟨⟨h, j⟩, ?_, ?_⟩
    · simp [starBasisGrade, cTensorOneHOneAddress]
    · change (Pi.basis (fun k : Fin H =>
          Module.finBasis K ((componentObj grading family a k).V 0))
        ⟨h, j⟩) = _
      rw [Pi.basis_apply, LinearMap.single_apply]
  · letI : Module K
        (∀ k : Fin H, (componentObj grading family a k).V 1) :=
      Pi.module _ _ _
    change (LinearMap.single K
      (fun k : Fin H => (componentObj grading family a k).V 1) h) x ∈ _
    rw [← (Module.finBasis K
      ((componentObj grading family a h).V 1)).sum_repr x]
    rw [map_sum]
    simp only [map_smul]
    apply Submodule.sum_mem
    intro j hj
    apply Submodule.smul_mem
    change (LinearMap.single K
      (fun k : Fin H => (componentObj grading family a k).V 1) h)
        ((Module.finBasis K
          ((componentObj grading family a h).V 1)) j) ∈
      cwBasisGrade (starBasis grading family a 1)
        (starBasisGrade grading family a 1) (Fin.castSucc h)
    unfold cwBasisGrade
    apply Submodule.subset_span
    refine ⟨⟨h, j⟩, ?_, ?_⟩
    · simp [starBasisGrade, cTensorOneHOneAddress]
    · change (Pi.basis (fun k : Fin H =>
          Module.finBasis K ((componentObj grading family a k).V 1))
        ⟨h, j⟩) = _
      rw [Pi.basis_apply, LinearMap.single_apply]
  · change (componentZEquiv grading family a h) x ∈
      cwBasisGrade (starBasis grading family a 2)
        (starBasisGrade grading family a 2) (Fin.last H)
    simpa only [starGrading, starBasisGrade,
      cTensorOneHOneAddress] using
      basisGrade_mem_of_const
        (starBasis grading family a 2) (Fin.last H)
        ((componentZEquiv grading family a h) x)

noncomputable def componentLift
    (family : CWQ6PrimaryHashFamily N L G A H)
    (a : Fin A) (h : Fin H) : ∀ i : Fin 3,
    (componentObj grading family a h).V i →ₗ[K]
      (starGrading grading family a).classOf i
        (cTensorOneHOneAddress H h i) :=
  fun i => LinearMap.codRestrict _
    (componentInclusion grading family a h i)
    (componentInclusion_mem grading family a h i)

theorem blockProj_component_same
    (family : CWQ6PrimaryHashFamily N L G A H)
    (a : Fin A) (h : Fin H) (i : Fin 3)
    (x : (componentObj grading family a h).V i) :
    (starGrading grading family a).blockProj i
        (cTensorOneHOneAddress H h i)
        (componentInclusion grading family a h i x) =
      componentLift grading family a h i x := by
  rw [TensorObj.TypeGrading.blockProj_apply_mem _ _ _ _
    (componentInclusion_mem grading family a h i x)]
  apply Subtype.ext
  rfl

theorem blockProj_component_ne_zero_mode0
    (family : CWQ6PrimaryHashFamily N L G A H)
    (a : Fin A) (h k : Fin H) (hhk : h ≠ k) :
    ((starGrading grading family a).blockProj 0
        (cTensorOneHOneAddress H h 0)).comp
        (componentInclusion grading family a k 0) = 0 := by
  apply LinearMap.ext
  intro x
  exact TensorObj.TypeGrading.blockProj_apply_mem_ne
    (starGrading grading family a) 0
    (cTensorOneHOneAddress H h 0)
    (cTensorOneHOneAddress H k 0)
    (by
      intro heq
      apply hhk
      exact Fin.castSucc_injective H heq)
    (componentInclusion grading family a k 0 x)
    (componentInclusion_mem grading family a k 0 x)

private theorem piTensorMap_eq_zero_of_coord
    {V W : Fin 3 → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (f : ∀ i, V i →ₗ[K] W i) (i : Fin 3) (hi : f i = 0)
    (x : PiTensorProduct K V) :
    PiTensorProduct.map f x = 0 := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod c v =>
      rw [map_smul, PiTensorProduct.map_tprod]
      suffices tprod K (fun j => f j (v j)) = 0 by simp [this]
      apply (PiTensorProduct.tprod K).map_coord_zero i
      rw [hi]
      rfl
  | add x y ihx ihy => simp [ihx, ihy]

theorem projected_component_eq_zero_of_ne
    (family : CWQ6PrimaryHashFamily N L G A H)
    (a : Fin A) (h k : Fin H) (hhk : h ≠ k) :
    PiTensorProduct.map
        (fun i => ((starGrading grading family a).blockProj i
          (cTensorOneHOneAddress H h i)).comp
            (componentInclusion grading family a k i))
        (componentObj grading family a k).t = 0 := by
  apply piTensorMap_eq_zero_of_coord _ 0
  exact blockProj_component_ne_zero_mode0 grading family a h k hhk

theorem star_blockTensor_eq_component
    (family : CWQ6PrimaryHashFamily N L G A H)
    (a : Fin A) (h : Fin H) :
    (starGrading grading family a).blockTensor
        (cTensorOneHOneAddress H h) =
      PiTensorProduct.map (componentLift grading family a h)
        (componentObj grading family a h).t := by
  classical
  unfold TensorObj.TypeGrading.blockTensor
  change PiTensorProduct.map
      (fun i => (starGrading grading family a).blockProj i
        (cTensorOneHOneAddress H h i))
      (∑ k : Fin H,
        PiTensorProduct.map (componentInclusion grading family a k)
          (componentObj grading family a k).t) = _
  rw [map_sum]
  rw [Finset.sum_eq_single h]
  · change ((PiTensorProduct.map
        (fun i => (starGrading grading family a).blockProj i
          (cTensorOneHOneAddress H h i))).comp
        (PiTensorProduct.map (componentInclusion grading family a h)))
          (componentObj grading family a h).t = _
    rw [← PiTensorProduct.map_comp]
    have hmaps :
        (fun i => ((starGrading grading family a).blockProj i
          (cTensorOneHOneAddress H h i)).comp
            (componentInclusion grading family a h i)) =
          componentLift grading family a h := by
      funext i
      apply LinearMap.ext
      intro x
      exact blockProj_component_same grading family a h i x
    rw [hmaps]
  · intro k _ hkh
    change ((PiTensorProduct.map
        (fun i => (starGrading grading family a).blockProj i
          (cTensorOneHOneAddress H h i))).comp
        (PiTensorProduct.map (componentInclusion grading family a k)))
          (componentObj grading family a k).t = 0
    rw [← PiTensorProduct.map_comp]
    exact projected_component_eq_zero_of_ne grading family a h k hkh.symm
  · exact fun hh => (hh (Finset.mem_univ h)).elim

noncomputable def componentDrop
    (family : CWQ6PrimaryHashFamily N L G A H)
    (a : Fin A) (h : Fin H) : ∀ i : Fin 3,
    (starGrading grading family a).classOf i
        (cTensorOneHOneAddress H h i) →ₗ[K]
      (componentObj grading family a h).V i
  | 0 => (LinearMap.proj (R := K)
      (φ := fun k : Fin H => (componentObj grading family a k).V 0) h).comp
      ((starGrading grading family a).classOf 0
        (cTensorOneHOneAddress H h 0)).subtype
  | 1 => (LinearMap.proj (R := K)
      (φ := fun k : Fin H => (componentObj grading family a k).V 1) h).comp
      ((starGrading grading family a).classOf 1
        (cTensorOneHOneAddress H h 1)).subtype
  | 2 => (componentZEquiv grading family a h).symm.toLinearMap.comp
      ((starGrading grading family a).classOf 2
        (cTensorOneHOneAddress H h 2)).subtype

theorem componentDrop_comp_lift
    (family : CWQ6PrimaryHashFamily N L G A H)
    (a : Fin A) (h : Fin H) (i : Fin 3) :
    (componentDrop grading family a h i).comp
        (componentLift grading family a h i) =
      LinearMap.id := by
  apply LinearMap.ext
  intro x
  fin_cases i
  · change ((LinearMap.single K
      (fun k : Fin H => (componentObj grading family a k).V 0) h) x) h = x
    rw [LinearMap.single_apply]
    simp
  · change ((LinearMap.single K
      (fun k : Fin H => (componentObj grading family a k).V 1) h) x) h = x
    rw [LinearMap.single_apply]
    simp
  · simp only [componentDrop, componentLift, LinearMap.comp_apply,
      componentInclusion, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.id_apply]
    exact (componentZEquiv grading family a h).symm_apply_apply x

theorem component_block_isomorphic
    (family : CWQ6PrimaryHashFamily N L G A H)
    (a : Fin A) (h : Fin H) :
    TensorObj.Isomorphic
      (componentObj grading family a h)
      ((starGrading grading family a).blockSubtensor
        (cTensorOneHOneAddress H h)) := by
  constructor
  · refine ⟨componentDrop grading family a h, ?_⟩
    change PiTensorProduct.map (componentDrop grading family a h)
      ((starGrading grading family a).blockTensor
        (cTensorOneHOneAddress H h)) = _
    rw [star_blockTensor_eq_component grading family a h]
    change PiTensorProduct.map (componentDrop grading family a h)
        (PiTensorProduct.map (componentLift grading family a h)
          (componentObj grading family a h).t) = _
    change ((PiTensorProduct.map (componentDrop grading family a h)).comp
      (PiTensorProduct.map (componentLift grading family a h)))
        (componentObj grading family a h).t = _
    rw [← PiTensorProduct.map_comp]
    have hmaps :
        (fun i => (componentDrop grading family a h i).comp
          (componentLift grading family a h i)) =
          fun _ => LinearMap.id := by
      funext i
      exact componentDrop_comp_lift grading family a h i
    rw [hmaps, PiTensorProduct.map_id]
    rfl
  · refine ⟨componentLift grading family a h, ?_⟩
    exact (star_blockTensor_eq_component grading family a h).symm

end SharedZStar

end CoupledCTensorPackaging

namespace CoupledCTensorPackaging

variable {K : Type u} [Field K]

private theorem interchange_tprod_outer
    {V W : Fin 3 → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (v : ∀ i, V i) (w : ∀ i, W i) :
    interchange (tprod K v) (tprod K w) =
      tprod K (fun i => v i ⊗ₜ[K] w i) := by
  show (interchange (tprod K v)) (tprod K w) = _
  unfold interchange
  rw [PiTensorProduct.lift.tprod]
  show (PiTensorProduct.lift (interchangeInner v)) (tprod K w) = _
  rw [PiTensorProduct.lift.tprod]
  rfl

private theorem map_interchange_outer
    {V₁ V₂ V₃ V₄ : Fin 3 → Type u}
    [∀ i, AddCommGroup (V₁ i)] [∀ i, Module K (V₁ i)]
    [∀ i, AddCommGroup (V₂ i)] [∀ i, Module K (V₂ i)]
    [∀ i, AddCommGroup (V₃ i)] [∀ i, Module K (V₃ i)]
    [∀ i, AddCommGroup (V₄ i)] [∀ i, Module K (V₄ i)]
    (f : ∀ i, V₁ i →ₗ[K] V₃ i) (g : ∀ i, V₂ i →ₗ[K] V₄ i)
    (t₁ : PiTensorProduct K V₁) (t₂ : PiTensorProduct K V₂) :
    PiTensorProduct.map (fun i => TensorProduct.map (f i) (g i))
        (interchange t₁ t₂) =
      interchange (PiTensorProduct.map f t₁)
        (PiTensorProduct.map g t₂) := by
  induction t₁ using PiTensorProduct.induction_on with
  | smul_tprod c v =>
      induction t₂ using PiTensorProduct.induction_on with
      | smul_tprod c' v' =>
          simp only [map_smul, LinearMap.smul_apply]
          rw [interchange_tprod_outer, PiTensorProduct.map_tprod,
            PiTensorProduct.map_tprod, PiTensorProduct.map_tprod,
            interchange_tprod_outer]
          simp only [TensorProduct.map_tmul]
      | add x y ih₁ ih₂ =>
          simp only [map_add, LinearMap.add_apply, ih₁, ih₂]
  | add x y ih₁ ih₂ =>
      simp only [map_add, LinearMap.add_apply, ih₁, ih₂]

theorem map_addressProj_outer
    {T : TensorObj K 3} {t R : ℕ}
    (grading : T.TypeGrading t) (address : Fin 3 → Fin R → Fin t) :
    PiTensorProduct.map (gradedAddressProj grading R address)
        (T.kronPow R).t =
      (gradedAddressBlock grading address).t := by
  induction R with
  | zero =>
      change PiTensorProduct.map (fun _ => LinearMap.id)
          (TensorObj.oneObj : TensorObj K 3).t =
        (TensorObj.oneObj : TensorObj K 3).t
      rw [PiTensorProduct.map_id]
      rfl
  | succ R ih =>
      change PiTensorProduct.map
          (fun i => TensorProduct.map
            (grading.blockProj i (address i 0))
            (gradedAddressProj grading R
              (fun i' j => address i' j.succ) i))
          (interchange T.t (T.kronPow R).t) =
        interchange
          (grading.blockTensor (fun i => address i 0))
          (gradedAddressBlock grading
            (fun i j => address i j.succ)).t
      rw [map_interchange_outer]
      unfold TensorObj.TypeGrading.blockTensor
      rw [ih]

theorem gradedAddressBlock_t_eq_zero_of_coord_outer
    {T : TensorObj K 3} {t R : ℕ}
    (grading : T.TypeGrading t) (address : Fin 3 → Fin R → Fin t)
    (r : Fin R)
    (hr : grading.blockTensor (fun i => address i r) = 0) :
    (gradedAddressBlock grading address).t = 0 := by
  induction R with
  | zero => exact Fin.elim0 r
  | succ R ih =>
      refine Fin.cases
        (motive := fun r =>
          grading.blockTensor (fun i => address i r) = 0 →
            (gradedAddressBlock grading address).t = 0)
        ?_ (fun r' => ?_) r hr
      · intro hr0
        change interchange (grading.blockTensor (fun i => address i 0))
            (gradedAddressBlock grading
              (fun i j => address i j.succ)).t = 0
        rw [hr0]
        simp only [map_zero, LinearMap.zero_apply]
      · intro hr'
        change interchange (grading.blockTensor (fun i => address i 0))
            (gradedAddressBlock grading
              (fun i j => address i j.succ)).t = 0
        have htail :
            (gradedAddressBlock grading
              (fun i j => address i j.succ)).t = 0 :=
          ih (fun i j => address i j.succ) r' hr'
        rw [htail]
        exact LinearMap.map_zero _

theorem map_sum_modes_dependent
    {J : Fin 3 → Type*} [∀ i, Fintype (J i)]
    {V W : Fin 3 → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (f : ∀ i, J i → V i →ₗ[K] W i)
    (x : PiTensorProduct K V) :
    PiTensorProduct.map (fun i => ∑ j, f i j) x =
      ∑ js : ∀ i, J i,
        PiTensorProduct.map (fun i => f i (js i)) x := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod c v =>
      simp only [map_smul, LinearMap.smul_apply, Finset.sum_smul]
      congr 1
      simp only [PiTensorProduct.map_tprod, LinearMap.coe_sum,
        Finset.sum_apply]
      rw [MultilinearMap.map_sum (PiTensorProduct.tprod K) _]
      rw [Finset.smul_sum]
  | add x y ihx ihy =>
      simp only [map_add, ihx, ihy, Finset.sum_add_distrib]

theorem bigAdd_t_eq_sum_slot_outer :
    ∀ (k : ℕ) (B : Fin k → TensorObj K 3),
      (TensorObj.bigAdd B).t =
        ∑ j : Fin k,
          PiTensorProduct.map
            (fun i => gradedBigAddSlot k B j i) (B j).t
  | 0, _ => by
      change (TensorObj.zeroObj : TensorObj K 3).t = ∑ j : Fin 0, _
      simp only [Finset.univ_eq_empty, Finset.sum_empty]
      rfl
  | 1, B => by
      change (B 0).t =
        ∑ j : Fin 1,
          PiTensorProduct.map
            (fun i => gradedBigAddSlot 1 B j i) (B j).t
      rw [Fin.sum_univ_one]
      change (B 0).t =
        PiTensorProduct.map (fun _ => LinearMap.id) (B 0).t
      rw [PiTensorProduct.map_id]
      rfl
  | n + 2, B => by
      change PiTensorProduct.map (fun i =>
              LinearMap.inl K ((B 0).V i)
                ((TensorObj.bigAdd (fun j => B j.succ)).V i)) (B 0).t +
          PiTensorProduct.map (fun i =>
              LinearMap.inr K ((B 0).V i)
                ((TensorObj.bigAdd (fun j => B j.succ)).V i))
            (TensorObj.bigAdd (fun j => B j.succ)).t =
        ∑ j : Fin (n + 2),
          PiTensorProduct.map
            (fun i => gradedBigAddSlot (n + 2) B j i) (B j).t
      rw [Fin.sum_univ_succ]
      rw [bigAdd_t_eq_sum_slot_outer (n + 1) (fun j => B j.succ)]
      congr 1
      rw [map_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [← LinearMap.comp_apply, ← PiTensorProduct.map_comp]
      rfl

variable {T : TensorObj K 3} (grading : T.TypeGrading 3)
variable {N L G A H : ℕ}

@[reducible] def outerChoiceType : Fin 3 → Type
  | 0 => Fin A × Fin H
  | 1 => Fin A × Fin H
  | 2 => Fin A

private instance outerChoiceFintype (i : Fin 3) :
    Fintype (outerChoiceType (A := A) (H := H) i) := by
  exact match i with
  | 0 => inferInstance
  | 1 => inferInstance
  | 2 => inferInstance

private noncomputable instance outerChoiceDecidableEq (i : Fin 3) :
    DecidableEq (outerChoiceType (A := A) (H := H) i) := by
  exact match i with
  | 0 => inferInstance
  | 1 => inferInstance
  | 2 => inferInstance

noncomputable def outerExtractionSummand
    (family : CWQ6PrimaryHashFamily N L G A H) :
    ∀ i : Fin 3, outerChoiceType (A := A) (H := H) i →
      (T.kronPow (2 * N)).V i →ₗ[K]
        (TensorObj.bigAdd (starObj grading family)).V i
  | 0, p =>
      (gradedBigAddSlot A (starObj grading family) p.1 0).comp
        ((componentInclusion grading family p.1 p.2 0).comp
          (gradedAddressProj grading (2 * N)
            (componentAddress family p.1 p.2) 0))
  | 1, p =>
      (gradedBigAddSlot A (starObj grading family) p.1 1).comp
        ((componentInclusion grading family p.1 p.2 1).comp
          (gradedAddressProj grading (2 * N)
            (componentAddress family p.1 p.2) 1))
  | 2, a =>
      (gradedBigAddSlot A (starObj grading family) a 2).comp
        (gradedAddressProj grading (2 * N)
          (componentAddress family a (firstFiberIndex family)) 2)

noncomputable def outerExtractionMap
    (family : CWQ6PrimaryHashFamily N L G A H) (i : Fin 3) :
    (T.kronPow (2 * N)).V i →ₗ[K]
      (TensorObj.bigAdd (starObj grading family)).V i :=
  ∑ j, outerExtractionSummand grading family i j

def outerDiagonalChoice
    (a : Fin A) (h : Fin H) :
    ∀ i : Fin 3, outerChoiceType (A := A) (H := H) i
  | 0 => (a, h)
  | 1 => (a, h)
  | 2 => a

def outerChosenAddress
    (family : CWQ6PrimaryHashFamily N L G A H)
    (js : ∀ i : Fin 3, outerChoiceType (A := A) (H := H) i) :
    Fin 3 → CWQ6CoupledAddress N
  | 0 => componentAddress family (js 0).1 (js 0).2
  | 1 => componentAddress family (js 1).1 (js 1).2
  | 2 => componentAddress family (js 2) (firstFiberIndex family)

def outerMixedAddress
    (family : CWQ6PrimaryHashFamily N L G A H)
    (js : ∀ i : Fin 3, outerChoiceType (A := A) (H := H) i) :
    CWQ6CoupledAddress N :=
  fun i r => outerChosenAddress family js i i r

theorem outerMixedSupported_implies_diagonal
    (family : CWQ6PrimaryHashFamily N L G A H)
    (js : ∀ i : Fin 3, outerChoiceType (A := A) (H := H) i)
    (hsupported : CWQ6CoupledCoordinatewiseSupported
      (outerMixedAddress family js)) :
    ∃ a : Fin A, ∃ h : Fin H,
      js = outerDiagonalChoice a h := by
  have hsupported' :
      CWQ6CoupledCoordinatewiseSupported
        (cwQ6CoupledMixedAddress
          (family.entry (js 0)).1
          (family.entry (js 1)).1
          (family.entry (js 2, firstFiberIndex family)).1) := by
    simpa only [outerMixedAddress, outerChosenAddress,
      componentAddress_eq_entry, cwQ6CoupledMixedAddress] using hsupported
  obtain ⟨hxy, hza⟩ := family.induced
    (js 0) (js 1) (js 2, firstFiberIndex family) hsupported'
  refine ⟨(js 0).1, (js 0).2, ?_⟩
  funext i
  fin_cases i
  · rfl
  · exact hxy.symm
  · exact hza.symm

theorem outerMixedSupported_of_all_nonzero
    (hSupport : ∀ σ : Fin 3 → Fin 3,
      σ ≠ ![0, 0, 0] → σ ≠ ![1, 1, 1] →
      σ ≠ ![0, 1, 2] → σ ≠ ![1, 0, 2] →
      grading.blockTensor σ = 0)
    (family : CWQ6PrimaryHashFamily N L G A H)
    (js : ∀ i : Fin 3, outerChoiceType (A := A) (H := H) i)
    (hall : ∀ r : Fin (2 * N),
      grading.blockTensor (fun i => outerMixedAddress family js i r) ≠ 0) :
    CWQ6CoupledCoordinatewiseSupported (outerMixedAddress family js) := by
  intro r
  let σ : Fin 3 → Fin 3 := fun i => outerMixedAddress family js i r
  by_cases h000 : σ = ![0, 0, 0]
  · left
    simpa [σ] using congrArg (fun f : Fin 3 → Fin 3 =>
      (f 0, f 1, f 2)) h000
  by_cases h111 : σ = ![1, 1, 1]
  · right; left
    simpa [σ] using congrArg (fun f : Fin 3 → Fin 3 =>
      (f 0, f 1, f 2)) h111
  by_cases h012 : σ = ![0, 1, 2]
  · right; right; left
    simpa [σ] using congrArg (fun f : Fin 3 → Fin 3 =>
      (f 0, f 1, f 2)) h012
  by_cases h102 : σ = ![1, 0, 2]
  · right; right; right
    simpa [σ] using congrArg (fun f : Fin 3 → Fin 3 =>
      (f 0, f 1, f 2)) h102
  exact (hall r (hSupport σ h000 h111 h012 h102)).elim

noncomputable def outerTargetInclusion
    (family : CWQ6PrimaryHashFamily N L G A H)
    (js : ∀ i : Fin 3, outerChoiceType (A := A) (H := H) i) :
    ∀ i : Fin 3,
      (gradedAddressBlock grading (outerChosenAddress family js i)).V i →ₗ[K]
        (TensorObj.bigAdd (starObj grading family)).V i
  | 0 => (gradedBigAddSlot A (starObj grading family) (js 0).1 0).comp
      (componentInclusion grading family (js 0).1 (js 0).2 0)
  | 1 => (gradedBigAddSlot A (starObj grading family) (js 1).1 1).comp
      (componentInclusion grading family (js 1).1 (js 1).2 1)
  | 2 => gradedBigAddSlot A (starObj grading family) (js 2) 2

theorem outerSummand_factor
    (family : CWQ6PrimaryHashFamily N L G A H)
    (js : ∀ i : Fin 3, outerChoiceType (A := A) (H := H) i) :
    (fun i => outerExtractionSummand grading family i (js i)) =
      fun i => (outerTargetInclusion grading family js i).comp
        (gradedAddressProj grading (2 * N)
          (outerChosenAddress family js i) i) := by
  funext i
  fin_cases i <;> apply LinearMap.ext <;> intro x <;> rfl

theorem outerProjection_eq_zero_of_coord
    {R : ℕ} (addresses : Fin 3 → Fin 3 → Fin R → Fin 3)
    (r : Fin R)
    (hr : grading.blockTensor (fun i => addresses i i r) = 0) :
    PiTensorProduct.map
        (fun i => gradedAddressProj grading R (addresses i) i)
        (T.kronPow R).t = 0 := by
  induction R with
  | zero => exact Fin.elim0 r
  | succ R ih =>
      refine Fin.cases
        (motive := fun r =>
          grading.blockTensor (fun i => addresses i i r) = 0 →
          PiTensorProduct.map
              (fun i => gradedAddressProj grading (R + 1)
                (addresses i) i)
              (T.kronPow (R + 1)).t = 0)
        ?_ (fun r' => ?_) r hr
      · intro hr0
        simp only [gradedAddressProj, TensorObj.kronPow]
        change PiTensorProduct.map
            (fun i => TensorProduct.map
              (grading.blockProj i (addresses i i 0))
              (gradedAddressProj grading R
                (fun i' s => addresses i i' s.succ) i))
            (interchange T.t (T.kronPow R).t) = 0
        rw [map_interchange_outer]
        have hfirst :
            PiTensorProduct.map
                (fun i => grading.blockProj i (addresses i i 0)) T.t =
              grading.blockTensor (fun i => addresses i i 0) := rfl
        rw [hfirst, hr0]
        simp only [map_zero, LinearMap.zero_apply]
      · intro hr'
        simp only [gradedAddressProj, TensorObj.kronPow]
        change PiTensorProduct.map
            (fun i => TensorProduct.map
              (grading.blockProj i (addresses i i 0))
              (gradedAddressProj grading R
                (fun i' s => addresses i i' s.succ) i))
            (interchange T.t (T.kronPow R).t) = 0
        rw [map_interchange_outer]
        have htail := ih
          (fun i i' s => addresses i i' s.succ)
          r' hr'
        rw [htail]
        exact LinearMap.map_zero _

theorem outerMixedProjection_eq_zero_of_nondiagonal
    (hSupport : ∀ σ : Fin 3 → Fin 3,
      σ ≠ ![0, 0, 0] → σ ≠ ![1, 1, 1] →
      σ ≠ ![0, 1, 2] → σ ≠ ![1, 0, 2] →
      grading.blockTensor σ = 0)
    (family : CWQ6PrimaryHashFamily N L G A H)
    (js : ∀ i : Fin 3, outerChoiceType (A := A) (H := H) i)
    (hjs : ∀ a : Fin A, ∀ h : Fin H,
      js ≠ outerDiagonalChoice a h) :
    PiTensorProduct.map
        (fun i => gradedAddressProj grading (2 * N)
          (outerChosenAddress family js i) i)
        (T.kronPow (2 * N)).t = 0 := by
  have hbad : ∃ r : Fin (2 * N),
      grading.blockTensor (fun i => outerMixedAddress family js i r) = 0 := by
    by_contra h
    have hall : ∀ r : Fin (2 * N),
        grading.blockTensor
          (fun i => outerMixedAddress family js i r) ≠ 0 := by
      intro r hr
      exact h ⟨r, hr⟩
    obtain ⟨a, h0, hdiag⟩ := outerMixedSupported_implies_diagonal
      family js (outerMixedSupported_of_all_nonzero
        grading hSupport family js hall)
    exact hjs a h0 hdiag
  obtain ⟨r, hr⟩ := hbad
  exact outerProjection_eq_zero_of_coord grading
    (fun i => outerChosenAddress family js i) r hr

theorem outerMappedTerm_eq_zero_of_nondiagonal
    (hSupport : ∀ σ : Fin 3 → Fin 3,
      σ ≠ ![0, 0, 0] → σ ≠ ![1, 1, 1] →
      σ ≠ ![0, 1, 2] → σ ≠ ![1, 0, 2] →
      grading.blockTensor σ = 0)
    (family : CWQ6PrimaryHashFamily N L G A H)
    (js : ∀ i : Fin 3, outerChoiceType (A := A) (H := H) i)
    (hjs : ∀ a : Fin A, ∀ h : Fin H,
      js ≠ outerDiagonalChoice a h) :
    PiTensorProduct.map
        (fun i => outerExtractionSummand grading family i (js i))
        (T.kronPow (2 * N)).t = 0 := by
  rw [outerSummand_factor grading family js]
  rw [PiTensorProduct.map_comp, LinearMap.comp_apply]
  rw [outerMixedProjection_eq_zero_of_nondiagonal
    grading hSupport family js hjs]
  exact LinearMap.map_zero _

theorem modeEquiv_comp_addressProj
    {R : ℕ} (address address' : Fin 3 → Fin R → Fin 3)
    (i : Fin 3) (hi : address i = address' i) :
    (gradedAddressBlockModeEquiv grading R address address' i hi).toLinearMap.comp
        (gradedAddressProj grading R address i) =
      gradedAddressProj grading R address' i := by
  induction R with
  | zero => rfl
  | succ R ih =>
      simp only [gradedAddressBlockModeEquiv, gradedAddressProj]
      apply TensorProduct.ext'
      intro x y
      change
        (LinearEquiv.ofEq
          (grading.classOf i (address i 0))
          (grading.classOf i (address' i 0)) _
          (grading.blockProj i (address i 0) x)) ⊗ₜ[K]
            (gradedAddressBlockModeEquiv grading R
              (fun i' j => address i' j.succ)
              (fun i' j => address' i' j.succ) i _)
              (gradedAddressProj grading R
                (fun i' j => address i' j.succ) i y) =
          (grading.blockProj i (address' i 0) x) ⊗ₜ[K]
            gradedAddressProj grading R
              (fun i' j => address' i' j.succ) i y
      congr 1
      · have h0 : address i 0 = address' i 0 := congrFun hi 0
        apply Subtype.ext
        change
          ((grading.blockProj i (address i 0) x :
              grading.classOf i (address i 0)) : T.V i) =
            ((grading.blockProj i (address' i 0) x :
              grading.classOf i (address' i 0)) : T.V i)
        exact congrArg
          (fun r : Fin 3 =>
            ((grading.blockProj i r x : grading.classOf i r) : T.V i)) h0
      · have htail :
            (fun j : Fin R => address i j.succ) =
              (fun j : Fin R => address' i j.succ) := by
          funext j
          exact congrFun hi j.succ
        have hih := ih
          (fun i' j => address i' j.succ)
          (fun i' j => address' i' j.succ) htail
        exact LinearMap.congr_fun hih y

theorem outerDiagonalMappedTerm
    (family : CWQ6PrimaryHashFamily N L G A H)
    (a : Fin A) (h : Fin H) :
    PiTensorProduct.map
        (fun i => outerExtractionSummand grading family i
          (outerDiagonalChoice a h i))
        (T.kronPow (2 * N)).t =
      PiTensorProduct.map
        (fun i => gradedBigAddSlot A (starObj grading family) a i)
        (PiTensorProduct.map (componentInclusion grading family a h)
          (componentObj grading family a h).t) := by
  have hmaps :
      (fun i => outerExtractionSummand grading family i
        (outerDiagonalChoice a h i)) =
      fun i =>
        (gradedBigAddSlot A (starObj grading family) a i).comp
          ((componentInclusion grading family a h i).comp
            (gradedAddressProj grading (2 * N)
              (componentAddress family a h) i)) := by
    funext i
    fin_cases i
    · rfl
    · rfl
    · apply LinearMap.ext
      intro x
      change (gradedBigAddSlot A (starObj grading family) a 2)
          (gradedAddressProj grading (2 * N)
            (componentAddress family a (firstFiberIndex family)) 2 x) =
        (gradedBigAddSlot A (starObj grading family) a 2)
          (componentInclusion grading family a h 2
            (gradedAddressProj grading (2 * N)
              (componentAddress family a h) 2 x))
      congr 1
      have hshared :
          (componentInclusion grading family a h 2).comp
              (gradedAddressProj grading (2 * N)
                (componentAddress family a h) 2) =
            gradedAddressProj grading (2 * N)
              (componentAddress family a (firstFiberIndex family)) 2 := by
        change (componentZEquiv grading family a h).toLinearMap.comp
            (gradedAddressProj grading (2 * N)
              (componentAddress family a h) 2) = _
        exact modeEquiv_comp_addressProj
          grading (componentAddress family a h)
          (componentAddress family a (firstFiberIndex family)) 2 rfl
      exact congrArg (fun f => f x) hshared.symm
  rw [hmaps]
  rw [PiTensorProduct.map_comp, LinearMap.comp_apply]
  congr 1
  have hinner := LinearMap.congr_fun
    (PiTensorProduct.map_comp
      (componentInclusion grading family a h)
      (fun i => gradedAddressProj grading (2 * N)
        (componentAddress family a h) i))
    (T.kronPow (2 * N)).t
  exact hinner.trans (by
    rw [LinearMap.comp_apply]
    exact congrArg
      (fun z => PiTensorProduct.map
        (componentInclusion grading family a h) z)
      (map_addressProj_outer grading (componentAddress family a h)))

theorem bigAdd_starObj_t_eq_sum_components_outer
    (family : CWQ6PrimaryHashFamily N L G A H) :
    (TensorObj.bigAdd (starObj grading family)).t =
      ∑ p : Fin A × Fin H,
        PiTensorProduct.map
          (fun i => gradedBigAddSlot A (starObj grading family) p.1 i)
          (PiTensorProduct.map
            (componentInclusion grading family p.1 p.2)
            (componentObj grading family p.1 p.2).t) := by
  rw [bigAdd_t_eq_sum_slot_outer]
  simp_rw [show ∀ a : Fin A,
      (starObj grading family a).t =
        ∑ h : Fin H,
          PiTensorProduct.map
            (componentInclusion grading family a h)
            (componentObj grading family a h).t by
    intro a
    rfl]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  calc
    _ = ∑ h : Fin H,
        PiTensorProduct.map
          (fun i => gradedBigAddSlot A (starObj grading family) a i)
          (PiTensorProduct.map
            (componentInclusion grading family a h)
            (componentObj grading family a h).t) := by
      exact map_sum
        (PiTensorProduct.map
          (fun i => gradedBigAddSlot A (starObj grading family) a i))
        (fun h : Fin H =>
          PiTensorProduct.map
            (componentInclusion grading family a h)
            (componentObj grading family a h).t)
        Finset.univ
    _ = _ := by rfl

noncomputable def outerDiagonalChoicesCore :
    Finset (∀ i : Fin 3, outerChoiceType (A := A) (H := H) i) :=
  Finset.univ.image
    (fun p : Fin A × Fin H => outerDiagonalChoice p.1 p.2)

theorem sharedZ_outer_restrict_core
    (family : CWQ6PrimaryHashFamily N L G A H)
    (hSupport : ∀ σ : Fin 3 → Fin 3,
      σ ≠ ![0, 0, 0] → σ ≠ ![1, 1, 1] →
      σ ≠ ![0, 1, 2] → σ ≠ ![1, 0, 2] →
      grading.blockTensor σ = 0) :
    TensorObj.Restrict
      (TensorObj.bigAdd (starObj grading family))
      (T.kronPow (2 * N)) := by
  classical
  refine ⟨outerExtractionMap grading family, ?_⟩
  unfold outerExtractionMap
  rw [map_sum_modes_dependent]
  let term := fun js :
      (∀ i : Fin 3, outerChoiceType (A := A) (H := H) i) =>
    PiTensorProduct.map
      (fun i => outerExtractionSummand grading family i (js i))
      (T.kronPow (2 * N)).t
  let componentTerm := fun p : Fin A × Fin H =>
    PiTensorProduct.map
      (fun i => gradedBigAddSlot A (starObj grading family) p.1 i)
      (PiTensorProduct.map (componentInclusion grading family p.1 p.2)
        (componentObj grading family p.1 p.2).t)
  change (∑ js, term js) = (TensorObj.bigAdd (starObj grading family)).t
  have hsplit :
      (∑ js, term js) =
        (∑ js ∈ outerDiagonalChoicesCore (A := A) (H := H),
          term js) := by
    symm
    apply Finset.sum_subset
    · exact Finset.subset_univ _
    · intro js _ hnot
      apply outerMappedTerm_eq_zero_of_nondiagonal
        grading hSupport family js
      intro a h heq
      apply hnot
      exact Finset.mem_image.mpr
        ⟨(a, h), Finset.mem_univ (a, h), heq.symm⟩
  have hreindex :
      (∑ js ∈ outerDiagonalChoicesCore (A := A) (H := H),
          term js) =
        ∑ p : Fin A × Fin H, componentTerm p := by
    refine (Finset.sum_bij
      (fun p (_ : p ∈ (Finset.univ : Finset (Fin A × Fin H))) =>
        outerDiagonalChoice p.1 p.2)
      (fun p _ => Finset.mem_image.mpr
        ⟨p, Finset.mem_univ p, rfl⟩)
      ?_ ?_ ?_).symm
    · intro p _ q _ hpq
      exact congrFun hpq 0
    · intro js hjs
      obtain ⟨p, _, hp⟩ := Finset.mem_image.mp hjs
      exact ⟨p, Finset.mem_univ p, hp⟩
    · intro p _
      exact (outerDiagonalMappedTerm
        grading family p.1 p.2).symm
  rw [hsplit, hreindex]
  exact (bigAdd_starObj_t_eq_sum_components_outer
    grading family).symm

end CoupledCTensorPackaging
set_option autoImplicit false
set_option maxHeartbeats 1600000


namespace SharedZStarGradingAndBlocksAudit

variable {K : Type u} [Field K]

private theorem piTensorMap_eq_zero_of_coord
    {V W : Fin 3 → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (f : ∀ i, V i →ₗ[K] W i) (i : Fin 3) (hi : f i = 0)
    (x : PiTensorProduct K V) :
    PiTensorProduct.map f x = 0 := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod c v =>
      rw [map_smul, PiTensorProduct.map_tprod]
      suffices tprod K (fun j => f j (v j)) = 0 by simp [this]
      apply (PiTensorProduct.tprod K).map_coord_zero i
      rw [hi]
      rfl
  | add x y ihx ihy => simp [ihx, ihy]

theorem projected_component_eq_zero_of_address_ne
    {T : TensorObj K 3} (grading : T.TypeGrading 3)
    {N L G A H : ℕ}
    (family : CWQ6PrimaryHashFamily N L G A H)
    (a : Fin A) (h : Fin H) (σ : Fin 3 → Fin (H + 1))
    (hne : σ ≠ cTensorOneHOneAddress H h) :
    PiTensorProduct.map
        (fun i => ((CoupledCTensorPackaging.starGrading grading family a).blockProj
          i (σ i)).comp
            (CoupledCTensorPackaging.componentInclusion grading family a h i))
        (CoupledCTensorPackaging.componentObj grading family a h).t = 0 := by
  classical
  have hcoord : ∃ i : Fin 3, σ i ≠ cTensorOneHOneAddress H h i := by
    by_contra hn
    push_neg at hn
    exact hne (funext hn)
  obtain ⟨i, hi⟩ := hcoord
  apply piTensorMap_eq_zero_of_coord _ i
  apply LinearMap.ext
  intro x
  exact TensorObj.TypeGrading.blockProj_apply_mem_ne
    (CoupledCTensorPackaging.starGrading grading family a)
    i (σ i) (cTensorOneHOneAddress H h i) hi
    (CoupledCTensorPackaging.componentInclusion grading family a h i x)
    (CoupledCTensorPackaging.componentInclusion_mem grading family a h i x)

theorem starGrading_supported
    {T : TensorObj K 3} (grading : T.TypeGrading 3)
    {N L G A H : ℕ}
    (family : CWQ6PrimaryHashFamily N L G A H)
    (a : Fin A) (σ : Fin 3 → Fin (H + 1))
    (hσ : σ ∉ Finset.univ.image (cTensorOneHOneAddress H)) :
    (CoupledCTensorPackaging.starGrading grading family a).blockTensor σ = 0 := by
  classical
  unfold TensorObj.TypeGrading.blockTensor
  change PiTensorProduct.map
      (fun i => (CoupledCTensorPackaging.starGrading grading family a).blockProj
        i (σ i))
      (∑ h : Fin H,
        PiTensorProduct.map
          (CoupledCTensorPackaging.componentInclusion grading family a h)
          (CoupledCTensorPackaging.componentObj grading family a h).t) = 0
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro h _
  change ((PiTensorProduct.map
      (fun i => (CoupledCTensorPackaging.starGrading grading family a).blockProj
        i (σ i))).comp
      (PiTensorProduct.map
        (CoupledCTensorPackaging.componentInclusion grading family a h)))
      (CoupledCTensorPackaging.componentObj grading family a h).t = 0
  rw [← PiTensorProduct.map_comp]
  apply projected_component_eq_zero_of_address_ne grading family a h σ
  intro heq
  apply hσ
  exact Finset.mem_image.mpr ⟨h, Finset.mem_univ h, heq.symm⟩

theorem sharedZ_star_grading_and_blocks
    {T : TensorObj K 3} (grading : T.TypeGrading 3)
    {N L G A H : ℕ}
    (family : CWQ6PrimaryHashFamily N L G A H) :
    ∀ a : Fin A,
      ∃ starGrading :
          (CoupledCTensorPackaging.starObj grading family a).TypeGrading (H + 1),
        (∀ σ : Fin 3 → Fin (H + 1),
          σ ∉ Finset.univ.image (cTensorOneHOneAddress H) →
            starGrading.blockTensor σ = 0) ∧
        ∀ h : Fin H,
          TensorObj.Isomorphic
            (gradedAddressBlock grading (family.entry (a, h)).1)
            (starGrading.blockSubtensor (cTensorOneHOneAddress H h)) := by
  intro a
  refine ⟨CoupledCTensorPackaging.starGrading grading family a, ?_, ?_⟩
  · exact starGrading_supported grading family a
  · intro h
    simpa only [CoupledCTensorPackaging.componentObj,
      CoupledCTensorPackaging.componentAddress_eq_entry] using
      CoupledCTensorPackaging.component_block_isomorphic grading family a h

end SharedZStarGradingAndBlocksAudit


namespace CoupledCTensorPackaging

variable {K : Type u} [Field K]
variable {T : TensorObj K 3} (grading : T.TypeGrading 3)
variable {N L G A H : ℕ}

theorem standalone_bigAdd_starObj_t_eq_sum_components
    (family : CWQ6PrimaryHashFamily N L G A H) :
    (TensorObj.bigAdd (starObj grading family)).t =
      ∑ p : Fin A × Fin H,
        PiTensorProduct.map
          (fun i => gradedBigAddSlot A (starObj grading family) p.1 i)
          (PiTensorProduct.map
            (componentInclusion grading family p.1 p.2)
            (componentObj grading family p.1 p.2).t) := by
  rw [bigAdd_t_eq_sum_slot_outer]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  change PiTensorProduct.map
      (fun i => gradedBigAddSlot A (starObj grading family) a i)
      (∑ h : Fin H,
        PiTensorProduct.map (componentInclusion grading family a h)
          (componentObj grading family a h).t) = _
  rw [map_sum]

noncomputable def standaloneOuterDiagonalChoices :
    Finset (∀ i : Fin 3, outerChoiceType (A := A) (H := H) i) :=
  Finset.univ.image (fun p : Fin A × Fin H =>
    outerDiagonalChoice p.1 p.2)

theorem standalone_sharedZ_outer_restrict
    (family : CWQ6PrimaryHashFamily N L G A H)
    (hSupport : ∀ sigma : Fin 3 → Fin 3,
      sigma ≠ ![0, 0, 0] → sigma ≠ ![1, 1, 1] →
      sigma ≠ ![0, 1, 2] → sigma ≠ ![1, 0, 2] →
      grading.blockTensor sigma = 0) :
    TensorObj.Restrict
      (TensorObj.bigAdd (starObj grading family))
      (T.kronPow (2 * N)) := by
  classical
  refine ⟨outerExtractionMap grading family, ?_⟩
  unfold outerExtractionMap
  rw [map_sum_modes_dependent]
  let term := fun js :
      (∀ i : Fin 3, outerChoiceType (A := A) (H := H) i) =>
    PiTensorProduct.map
      (fun i => outerExtractionSummand grading family i (js i))
      (T.kronPow (2 * N)).t
  let componentTerm := fun p : Fin A × Fin H =>
    PiTensorProduct.map
      (fun i => gradedBigAddSlot A (starObj grading family) p.1 i)
      (PiTensorProduct.map (componentInclusion grading family p.1 p.2)
        (componentObj grading family p.1 p.2).t)
  change (∑ js, term js) = (TensorObj.bigAdd (starObj grading family)).t
  have hsplit :
      (∑ js, term js) =
        (∑ js ∈ standaloneOuterDiagonalChoices (A := A) (H := H),
          term js) := by
    symm
    apply Finset.sum_subset
    · exact Finset.subset_univ _
    · intro js _ hnot
      apply outerMappedTerm_eq_zero_of_nondiagonal
        grading hSupport family js
      intro a h heq
      apply hnot
      exact Finset.mem_image.mpr
        ⟨(a, h), Finset.mem_univ (a, h), heq.symm⟩
  have hreindex :
      (∑ js ∈ standaloneOuterDiagonalChoices (A := A) (H := H),
        term js) =
        ∑ p : Fin A × Fin H, componentTerm p := by
    refine (Finset.sum_bij
      (fun p (_ : p ∈ (Finset.univ : Finset (Fin A × Fin H))) =>
        outerDiagonalChoice p.1 p.2)
      (fun p _ => Finset.mem_image.mpr
        ⟨p, Finset.mem_univ p, rfl⟩)
      ?_ ?_ ?_).symm
    · intro p _ q _ hpq
      have h0 := congrFun hpq 0
      exact Prod.ext (congrArg Prod.fst h0) (congrArg Prod.snd h0)
    · intro js hjs
      obtain ⟨p, _, hp⟩ := Finset.mem_image.mp hjs
      exact ⟨p, Finset.mem_univ p, hp⟩
    · intro p _
      exact (outerDiagonalMappedTerm grading family p.1 p.2).symm
  rw [hsplit, hreindex]
  exact (standalone_bigAdd_starObj_t_eq_sum_components grading family).symm

end CoupledCTensorPackaging

theorem solution
    {K : Type u} [Field K]
    (N L G A H : ℕ)
    (T : TensorObj K 3) (grading : T.TypeGrading 3)
    (hSupport : ∀ σ : Fin 3 → Fin 3,
      σ ≠ ![0, 0, 0] → σ ≠ ![1, 1, 1] →
      σ ≠ ![0, 1, 2] → σ ≠ ![1, 0, 2] →
      grading.blockTensor σ = 0)
    (family : CWQ6PrimaryHashFamily N L G A H) :
    ∃ star : Fin A → TensorObj K 3,
      TensorObj.Restrict (TensorObj.bigAdd star) (T.kronPow (2 * N)) ∧
      ∀ a : Fin A,
        ∃ starGrading : (star a).TypeGrading (H + 1),
          (∀ σ : Fin 3 → Fin (H + 1),
            σ ∉ Finset.univ.image (cTensorOneHOneAddress H) →
              starGrading.blockTensor σ = 0) ∧
          ∀ h : Fin H,
            TensorObj.Isomorphic
              (gradedAddressBlock grading (family.entry (a, h)).1)
              (starGrading.blockSubtensor
                (cTensorOneHOneAddress H h)) := by
  classical
  refine ⟨CoupledCTensorPackaging.starObj grading family, ?_, ?_⟩
  · exact CoupledCTensorPackaging.standalone_sharedZ_outer_restrict
      grading family hSupport
  · exact SharedZStarGradingAndBlocksAudit.sharedZ_star_grading_and_blocks
      grading family
