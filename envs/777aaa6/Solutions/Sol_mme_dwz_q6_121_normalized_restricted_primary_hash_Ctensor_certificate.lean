-- Prove2me | solution 1 for mme_dwz_q6_121_normalized_restricted_primary_hash_Ctensor_certificate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T13:20:12.786084+00:00
-- url     : https://prove2.me/submissions/0fcc448e-dea2-45fe-a153-60db34e2407b

import Theorems.Thm_mme_dwz_q6_121_normalized_primary_hash_star_restrict
import Theorems.Thm_mme_primary_hash_family_sharedZ_star_grading_components
import Theorems.Thm_mme_dwz_q6_explicit_coupled_four_block_isomorphisms
import Theorems.Thm_mme_coupled_four_block_exact_address_component_certificate
import Definitions.Def_CTensorOneHOneFamilyCertificate
import Definitions.Def_mme_permutation

open MME MME.TensorObj MME.DWZComponentRestriction
open CoupledCTensorPackaging

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

theorem solution
    {K : Type u} [Field K]
    (m L G A H : ℕ)
    (family : CWQ6PrimaryHashFamily
      (1036722900000000 * m) L G A H) :
    Nonempty
      (CTensorOneHOneFamilyCertificate
        (TensorObj.permObj cyclicPerm
          (restrictedComponentPower K (13 : Fin 15) m))
        A H (6 ^ (4 * G + 2 * L))) := by
  classical
  let G0 := dwzQ6CoupledGrading K
  let stars : Fin A → TensorObj K 3 := starObj G0 family
  have hrestrict : TensorObj.Restrict (TensorObj.bigAdd stars)
      (TensorObj.permObj cyclicPerm
        (restrictedComponentPower K (13 : Fin 15) m)) := by
    simpa [G0, stars] using
      mme_dwz_q6_121_normalized_primary_hash_star_restrict
        (K := K) m L G A H family
  have hstar :=
    mme_primary_hash_family_sharedZ_star_grading_components G0 family
  obtain ⟨h000, h111, h012, h102⟩ :=
    mme_dwz_q6_explicit_coupled_four_block_isomorphisms (K := K)
  refine ⟨{
    star := stars
    restrict := hrestrict
    certificate := ?_
  }⟩
  intro a
  let grading : (stars a).TypeGrading (H + 1) :=
    starGrading G0 family a
  have hsupported : ∀ σ : Fin 3 → Fin (H + 1),
      σ ∉ Finset.univ.image (cTensorOneHOneAddress H) →
        grading.blockTensor σ = 0 := by
    simpa [grading, stars] using (hstar a).1
  have hstarComponent : ∀ h : Fin H,
      TensorObj.Isomorphic
        (componentObj G0 family a h)
        (grading.blockSubtensor (cTensorOneHOneAddress H h)) := by
    intro h
    simpa [grading, stars] using (hstar a).2 h
  have hcomponent (h : Fin H) :
      ∃ x y z : ℕ,
        TensorObj.Isomorphic (MMObj K x y z)
          (grading.blockSubtensor (cTensorOneHOneAddress H h)) ∧
        x * y * z = 6 ^ (4 * G + 2 * L) := by
    obtain ⟨x, y, z, hiso, hvolume⟩ :=
      mme_coupled_four_block_exact_address_component_certificate
        6 (1036722900000000 * m) L G
        (coupledObj K 6) G0 h000 h111 h012 h102
        (family.entry (a, h))
    have hlocal : TensorObj.Isomorphic (MMObj K x y z)
        (componentObj G0 family a h) := by
      simpa [componentObj] using hiso
    exact ⟨x, y, z, hlocal.trans (hstarComponent h), hvolume⟩
  let x (h : Fin H) : ℕ := Classical.choose (hcomponent h)
  have hyz (h : Fin H) :
      ∃ y z : ℕ,
        TensorObj.Isomorphic (MMObj K (x h) y z)
          (grading.blockSubtensor (cTensorOneHOneAddress H h)) ∧
        x h * y * z = 6 ^ (4 * G + 2 * L) :=
    Classical.choose_spec (hcomponent h)
  let y (h : Fin H) : ℕ := Classical.choose (hyz h)
  have hz (h : Fin H) :
      ∃ z : ℕ,
        TensorObj.Isomorphic (MMObj K (x h) (y h) z)
          (grading.blockSubtensor (cTensorOneHOneAddress H h)) ∧
        x h * y h * z = 6 ^ (4 * G + 2 * L) :=
    Classical.choose_spec (hyz h)
  let z (h : Fin H) : ℕ := Classical.choose (hz h)
  have hxyz (h : Fin H) :
      TensorObj.Isomorphic (MMObj K (x h) (y h) (z h))
          (grading.blockSubtensor (cTensorOneHOneAddress H h)) ∧
        x h * y h * z h = 6 ^ (4 * G + 2 * L) :=
    Classical.choose_spec (hz h)
  exact {
    grading := grading
    supported := hsupported
    m := x
    n := y
    p := z
    component := fun h ↦ (hxyz h).1
    common_volume := fun h ↦ (hxyz h).2
  }
