-- Prove2me | solution 1 for mme_dwz_q6_112_primary_hash_family_restricted_component_Ctensor_certificate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T07:52:37.318272+00:00
-- url     : https://prove2.me/submissions/65415ae4-6f6f-4332-8a87-0b89fe2b621e

import Definitions.Def_CTensorOneHOneFamilyCertificate
import Definitions.Def_mme_CW_q6_primary_hash_family
import Definitions.Def_mme_dwz_table2_standard_obj
import Theorems.Thm_mme_dwz_q6_112_restricted_primary_star_assembly
import Theorems.Thm_mme_dwz_q6_explicit_coupled_four_block_isomorphisms
import Theorems.Thm_mme_coupled_four_block_exact_address_component_certificate

open MME
open MME.DWZComponentRestriction

universe u

set_option autoImplicit false
set_option warningAsError true

/-- The exact restricted enhanced-112 certificate follows from the
source-sensitive shared-Z star assembly and the four explicit local block
identifications. -/
theorem solution
    {K : Type u} [Field K] (m A H : ℕ)
    (family : CWQ6PrimaryHashFamily
      (50000000 * (20088623 * m))
      (21015 * (20088623 * m))
      (49978985 * (20088623 * m)) A H) :
    Nonempty
      (CTensorOneHOneFamilyCertificate
        (restrictedComponentPower K (12 : Fin 15) m) A H
        (6 ^
          (4 * (49978985 * (20088623 * m)) +
            2 * (21015 * (20088623 * m))))) := by
  classical
  obtain ⟨star, hrestrict, hstar⟩ :=
    mme_dwz_q6_112_restricted_primary_star_assembly
      (K := K) m A H family
  obtain ⟨h000, h111, h012, h102⟩ :=
    mme_dwz_q6_explicit_coupled_four_block_isomorphisms (K := K)
  refine ⟨{
    star := star
    restrict := hrestrict
    certificate := ?_
  }⟩
  intro a
  let starGrading : (star a).TypeGrading (H + 1) :=
    Classical.choose (hstar a)
  have hstarSpec :
      (∀ σ : Fin 3 → Fin (H + 1),
        σ ∉ Finset.univ.image (cTensorOneHOneAddress H) →
          starGrading.blockTensor σ = 0) ∧
      ∀ h : Fin H,
        TensorObj.Isomorphic
          (gradedAddressBlock (dwzQ6CoupledGrading K)
            (family.entry (a, h)).1)
          (starGrading.blockSubtensor
            (cTensorOneHOneAddress H h)) :=
    Classical.choose_spec (hstar a)
  have hsupported := hstarSpec.1
  have hstarComponent := hstarSpec.2
  have hcomponent (h : Fin H) :
      ∃ x y z : ℕ,
        TensorObj.Isomorphic (MMObj K x y z)
          (starGrading.blockSubtensor (cTensorOneHOneAddress H h)) ∧
        x * y * z =
          6 ^
            (4 * (49978985 * (20088623 * m)) +
              2 * (21015 * (20088623 * m))) := by
    obtain ⟨x, y, z, hiso, hvolume⟩ :=
      mme_coupled_four_block_exact_address_component_certificate
        6
        (50000000 * (20088623 * m))
        (21015 * (20088623 * m))
        (49978985 * (20088623 * m))
        (coupledObj K 6) (dwzQ6CoupledGrading K)
        h000 h111 h012 h102 (family.entry (a, h))
    exact ⟨x, y, z, hiso.trans (hstarComponent h), hvolume⟩
  let x (h : Fin H) : ℕ := Classical.choose (hcomponent h)
  have hyz (h : Fin H) :
      ∃ y z : ℕ,
        TensorObj.Isomorphic (MMObj K (x h) y z)
          (starGrading.blockSubtensor (cTensorOneHOneAddress H h)) ∧
        x h * y * z =
          6 ^
            (4 * (49978985 * (20088623 * m)) +
              2 * (21015 * (20088623 * m))) :=
    Classical.choose_spec (hcomponent h)
  let y (h : Fin H) : ℕ := Classical.choose (hyz h)
  have hz (h : Fin H) :
      ∃ z : ℕ,
        TensorObj.Isomorphic (MMObj K (x h) (y h) z)
          (starGrading.blockSubtensor (cTensorOneHOneAddress H h)) ∧
        x h * y h * z =
          6 ^
            (4 * (49978985 * (20088623 * m)) +
              2 * (21015 * (20088623 * m))) :=
    Classical.choose_spec (hyz h)
  let z (h : Fin H) : ℕ := Classical.choose (hz h)
  have hxyz (h : Fin H) :
      TensorObj.Isomorphic (MMObj K (x h) (y h) (z h))
          (starGrading.blockSubtensor (cTensorOneHOneAddress H h)) ∧
        x h * y h * z h =
          6 ^
            (4 * (49978985 * (20088623 * m)) +
              2 * (21015 * (20088623 * m))) :=
    Classical.choose_spec (hz h)
  exact {
    grading := starGrading
    supported := hsupported
    m := x
    n := y
    p := z
    component := fun h ↦ (hxyz h).1
    common_volume := fun h ↦ (hxyz h).2
  }
