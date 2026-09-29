-- Prove2me | solution 1 for mme_coupled_four_block_exact_address_component_certificate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T05:22:26.520214+00:00
-- url     : https://prove2.me/submissions/ebabd43c-a639-41fc-ad7a-7dc3f582435e

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

end SharedZStar

end CoupledCTensorPackaging

theorem solution
    {K : Type u} [Field K]
    (q N L G : ℕ)
    (T : TensorObj K 3) (grading : T.TypeGrading 3)
    (h000 : TensorObj.Isomorphic (MMObj K 1 q 1)
      (grading.blockSubtensor ![0, 0, 0]))
    (h111 : TensorObj.Isomorphic (MMObj K 1 q 1)
      (grading.blockSubtensor ![1, 1, 1]))
    (h012 : TensorObj.Isomorphic (MMObj K q 1 q)
      (grading.blockSubtensor ![0, 1, 2]))
    (h102 : TensorObj.Isomorphic (MMObj K q 1 q)
      (grading.blockSubtensor ![1, 0, 2]))
    (address : CWQ6ExactCoupledAddress N L G) :
    ∃ m n p : ℕ,
      TensorObj.Isomorphic (MMObj K m n p)
        (gradedAddressBlock grading address.1) ∧
      m * n * p = q ^ (4 * G + 2 * L) := by
  let m := ∏ j : Fin (2 * N),
    CoupledCTensorPackaging.localM q
      (cwQ6CoupledAddressType address.1 j)
  let n := ∏ j : Fin (2 * N),
    CoupledCTensorPackaging.localN q
      (cwQ6CoupledAddressType address.1 j)
  let p := ∏ j : Fin (2 * N),
    CoupledCTensorPackaging.localP q
      (cwQ6CoupledAddressType address.1 j)
  refine ⟨m, n, p, ?_, ?_⟩
  · exact CoupledCTensorPackaging.exactAddressBlockIso
      grading q N L G h000 h111 h012 h102 address
  · exact CoupledCTensorPackaging.exactAddressCommonVolume
      q N L G address
