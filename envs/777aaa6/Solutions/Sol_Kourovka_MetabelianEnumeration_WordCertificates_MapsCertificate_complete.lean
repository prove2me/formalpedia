-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.WordCertificates.MapsCertificate.complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:01:57.338493+00:00
-- url     : https://prove2.me/submissions/8e0ae349-8f0d-42ba-a141-3c1aa83fad93

import Definitions.Def_Kourovka_Certificates_WordCertificates
import Definitions.Def_Kourovka_Certificates_PresentationIsomorphism
import Theorems.Thm_Kourovka_MetabelianEnumeration_WordCertificates_mk_lift_of_generator_images
import Theorems.Thm_Kourovka_MetabelianEnumeration_WordCertificates_hasDerivation_iff


set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.WordCertificates
namespace Kourovka.MetabelianEnumeration.WordCertificates
namespace MapsCertificate
theorem _root_.solution {n m : ℕ} (source : List (FreeGroup (Fin n)))
    (target : List (FreeGroup (Fin m)))
    (e : PresentedGroup (relSet source) ≃* PresentedGroup (relSet target)) :
    ∃ cert : MapsCertificate source target, cert.check = true := by
  classical
  choose f hf using fun i : Fin n =>
    PresentedGroup.mk_surjective (relSet target) (e (PresentedGroup.of i))
  choose g hg using fun i : Fin m =>
    PresentedGroup.mk_surjective (relSet source) (e.symm (PresentedGroup.of i))
  have hF := mk_lift_of_generator_images source target e.toMonoidHom f hf
  have hG := mk_lift_of_generator_images target source e.symm.toMonoidHom g hg
  have hs : ∀ i : Fin source.length,
      FreeGroup.lift f source[i] ∈ Subgroup.normalClosure (relSet target) := by
    intro i
    apply PresentedGroup.mk_eq_one_iff.mp
    rw [hF, PresentedGroup.one_of_mem (by simp [relSet])]
    exact e.map_one
  have ht : ∀ i : Fin target.length,
      FreeGroup.lift g target[i] ∈ Subgroup.normalClosure (relSet source) := by
    intro i
    apply PresentedGroup.mk_eq_one_iff.mp
    rw [hG, PresentedGroup.one_of_mem (by simp [relSet])]
    exact e.symm.map_one
  have hi : ∀ i : Fin n, FreeGroup.lift g (f i) * (FreeGroup.of i)⁻¹ ∈
      Subgroup.normalClosure (relSet source) := by
    intro i
    apply PresentedGroup.mk_eq_one_iff.mp
    rw [map_mul, map_inv, hG, hf]
    simp only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply, PresentedGroup.of,
      mul_inv_cancel]
  have hj : ∀ i : Fin m, FreeGroup.lift f (g i) * (FreeGroup.of i)⁻¹ ∈
      Subgroup.normalClosure (relSet target) := by
    intro i
    apply PresentedGroup.mk_eq_one_iff.mp
    rw [map_mul, map_inv, hF, hg]
    simp only [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply, PresentedGroup.of,
      mul_inv_cancel]
  choose ds hds using fun i => (hasDerivation_iff target _).mpr (hs i)
  choose dt hdt using fun i => (hasDerivation_iff source _).mpr (ht i)
  choose di hdi using fun i => (hasDerivation_iff source _).mpr (hi i)
  choose dj hdj using fun i => (hasDerivation_iff target _).mpr (hj i)
  refine ⟨⟨fun i => (f i).toWord, fun i => (g i).toWord, ds, dt, di, dj⟩, ?_⟩
  simp only [MapsCertificate.check, MapsCertificate.forwardMap, MapsCertificate.backwardMap,
    FreeGroup.mk_toWord, decide_eq_true_eq]
  exact ⟨hds, hdt, hdi, hdj⟩
end MapsCertificate
end Kourovka.MetabelianEnumeration.WordCertificates
