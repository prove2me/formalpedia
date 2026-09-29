-- Prove2me | solution 1 for mme_CW_q6_primary_hash_family_uniform_MM_dimensions
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T07:12:58.476657+00:00
-- url     : https://prove2.me/submissions/82eb50ad-2119-47b8-a8fa-5c91ecd65632

import Definitions.Def_CTensorOneHOneFamilyCertificate
import Definitions.Def_mme_CW_q6_primary_hash_family
import Definitions.Def_mme_induced_word_zeroing
import Definitions.Def_mme_TypeGrading_kron
import Theorems.Thm_mme_kronFin_MMObj_iso
import Theorems.Thm_mme_kronFin_respects_iso
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic
import Theorems.Thm_mme_primary_hash_family_sharedZ_Ctensor_star_assembly
import Theorems.Thm_mme_CW_coupled_three_grading_isomorphism_certificate

open MME PiTensorProduct BigOperators Module

universe u


namespace UniformAddressShape

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


end UniformAddressShape


open MME UniformAddressShape BigOperators
set_option autoImplicit false

/-- Every supported exact address has the same three matrix dimensions. -/
theorem mme_coupled_four_block_exact_address_dimensions
    (q N L G : ℕ) (address : CWQ6ExactCoupledAddress N L G) :
    (∏ j : Fin (2 * N), localM q (cwQ6CoupledAddressType address.1 j)) = q ^ (2 * G) ∧
    (∏ j : Fin (2 * N), localN q (cwQ6CoupledAddressType address.1 j)) = q ^ (2 * L) ∧
    (∏ j : Fin (2 * N), localP q (cwQ6CoupledAddressType address.1 j)) = q ^ (2 * G) := by
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
    rw [← Finset.prod_filter]; simp only [Finset.prod_const]
    rw [hzcount 2]
    simp [cwQ6CoupledMarginalMultiplicity]
  have hp :
      (∏ j : Fin (2 * N),
        localP q (cwQ6CoupledAddressType address.1 j)) = q ^ (2 * G) := by
    change (∏ j : Fin (2 * N), if zword j = 2 then q else 1) = _
    rw [← Finset.prod_filter]; simp only [Finset.prod_const]
    rw [hzcount 2]
    simp [cwQ6CoupledMarginalMultiplicity]
  have hnpoint (j : Fin (2 * N)) :
      localN q (cwQ6CoupledAddressType address.1 j) =
        (if zword j = 0 then q else 1) *
          (if zword j = 1 then q else 1) := by
    change (if zword j = 2 then 1 else q) = _
    generalize hz : zword j = z
    fin_cases z <;> simp
  have hn :
      (∏ j : Fin (2 * N),
        localN q (cwQ6CoupledAddressType address.1 j)) = q ^ L * q ^ L := by
    simp_rw [hnpoint, Finset.prod_mul_distrib]
    rw [← Finset.prod_filter, ← Finset.prod_filter]
    simp only [Finset.prod_const]
    rw [hzcount 0, hzcount 1]
    simp [cwQ6CoupledMarginalMultiplicity]
  refine ⟨hm, ?_, hp⟩
  rw [hn, ← pow_add]
  congr 1
  omega

/-- The exact matrix shape of each coupled four-block address. -/
theorem mme_coupled_four_block_exact_address_MM_isomorphic
    {K : Type u} [Field K] (q N L G : ℕ)
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
    TensorObj.Isomorphic (MMObj K (q ^ (2 * G)) (q ^ (2 * L)) (q ^ (2 * G)))
      (gradedAddressBlock grading address.1) := by
  have h := exactAddressBlockIso grading q N L G h000 h111 h012 h102 address
  obtain ⟨hm, hn, hp⟩ := mme_coupled_four_block_exact_address_dimensions q N L G address
  simpa only [hm, hn, hp] using h


/-- The primary hash stars can be chosen with identical matrix dimensions at every leaf. -/
theorem solution
    {K : Type u} [Field K] (N L G A H : ℕ)
    (family : CWQ6PrimaryHashFamily N L G A H) :
    ∃ cert : CTensorOneHOneFamilyCertificate
        ((coupledObj K 6).kronPow (2 * N)) A H (6 ^ (4 * G + 2 * L)),
      ∀ a h, (cert.certificate a).m h = 6 ^ (2 * G) ∧
        (cert.certificate a).n h = 6 ^ (2 * L) ∧
        (cert.certificate a).p h = 6 ^ (2 * G) := by
  classical
  obtain ⟨grading, hsupport, h000, h111, h012, h102⟩ :=
    mme_CW_coupled_three_grading_isomorphism_certificate (K := K) 6
  obtain ⟨star, hrestrict, hstar⟩ :=
    mme_primary_hash_family_sharedZ_Ctensor_star_assembly
      N L G A H (coupledObj K 6) grading hsupport family
  let certificates : ∀ a, CTensorOneHOneCertificate (star a) H (6 ^ (4 * G + 2 * L)) :=
    fun a ↦ {
      grading := Classical.choose (hstar a)
      supported := (Classical.choose_spec (hstar a)).1
      m := fun _ ↦ 6 ^ (2 * G)
      n := fun _ ↦ 6 ^ (2 * L)
      p := fun _ ↦ 6 ^ (2 * G)
      component := fun h ↦
        (mme_coupled_four_block_exact_address_MM_isomorphic
          6 N L G (coupledObj K 6) grading h000 h111 h012 h102
          (family.entry (a, h))).trans ((Classical.choose_spec (hstar a)).2 h)
      common_volume := fun _ ↦ by
        simp only [← pow_add]
        congr 1
        omega }
  exact ⟨{ star := star, restrict := hrestrict, certificate := certificates },
    fun _ _ ↦ ⟨rfl, rfl, rfl⟩⟩


#print axioms solution
