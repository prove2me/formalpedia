-- Prove2me | solution 1 for mme_coupled_four_block_induced_family_Ctensor_certificates_design
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T05:24:37.889593+00:00
-- url     : https://prove2.me/submissions/c258ca4e-25c1-484b-b8d7-873e51f7483b

import Theorems.Thm_mme_primary_hash_family_sharedZ_Ctensor_star_assembly
import Theorems.Thm_mme_coupled_four_block_exact_address_component_certificate

open MME

universe u

theorem solution
    {K : Type u} [Field K]
    (q N L G A H : ℕ)
    (T : TensorObj K 3) (grading : T.TypeGrading 3)
    (hSupport : ∀ σ : Fin 3 → Fin 3,
      σ ≠ ![0, 0, 0] → σ ≠ ![1, 1, 1] →
      σ ≠ ![0, 1, 2] → σ ≠ ![1, 0, 2] →
      grading.blockTensor σ = 0)
    (h000 : TensorObj.Isomorphic (MMObj K 1 q 1)
      (grading.blockSubtensor ![0, 0, 0]))
    (h111 : TensorObj.Isomorphic (MMObj K 1 q 1)
      (grading.blockSubtensor ![1, 1, 1]))
    (h012 : TensorObj.Isomorphic (MMObj K q 1 q)
      (grading.blockSubtensor ![0, 1, 2]))
    (h102 : TensorObj.Isomorphic (MMObj K q 1 q)
      (grading.blockSubtensor ![1, 0, 2]))
    (family : CWQ6PrimaryHashFamily N L G A H) :
    Nonempty
      (CTensorOneHOneFamilyCertificate
        (T.kronPow (2 * N)) A H (q ^ (4 * G + 2 * L))) := by
  classical
  obtain ⟨star, hrestrict, hstar⟩ :=
    mme_primary_hash_family_sharedZ_Ctensor_star_assembly
      N L G A H T grading hSupport family
  refine ⟨{
    star := star
    restrict := hrestrict
    certificate := ?_
  }⟩
  intro a
  let starGrading := Classical.choose (hstar a)
  have hstarSpec := Classical.choose_spec (hstar a)
  have hsupported := hstarSpec.1
  have hblock := hstarSpec.2
  have hdata : ∀ h : Fin H, ∃ m n p : ℕ,
      TensorObj.Isomorphic (MMObj K m n p)
        (gradedAddressBlock grading (family.entry (a, h)).1) ∧
      m * n * p = q ^ (4 * G + 2 * L) := by
    intro h
    exact mme_coupled_four_block_exact_address_component_certificate
      q N L G T grading h000 h111 h012 h102 (family.entry (a, h))
  let m : Fin H → ℕ := fun h => Classical.choose (hdata h)
  let hm (h : Fin H) := Classical.choose_spec (hdata h)
  let n : Fin H → ℕ := fun h => Classical.choose (hm h)
  let hn (h : Fin H) := Classical.choose_spec (hm h)
  let p : Fin H → ℕ := fun h => Classical.choose (hn h)
  have hspec (h : Fin H) := Classical.choose_spec (hn h)
  exact {
    grading := starGrading
    supported := hsupported
    m := m
    n := n
    p := p
    component := fun h => (hspec h).1.trans (hblock h)
    common_volume := fun h => (hspec h).2
  }
