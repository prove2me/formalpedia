-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.WordCertificates.finite_relator_quotient_of_surjection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:02:46.746745+00:00
-- url     : https://prove2.me/submissions/fc3b5c20-66d6-460e-afc4-29fbc2b2dffc

import Definitions.Def_Kourovka_Certificates_PresentationIsomorphism
import Definitions.Def_Kourovka_Presentations_FiniteQuotient
import Theorems.Thm_Kourovka_MetabelianEnumeration_WordCertificates_exists_iso_of_maps
import Theorems.Thm_Kourovka_MetabelianEnumeration_WordCertificates_mk_lift_of_generator_images


set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.WordCertificates
namespace Kourovka.MetabelianEnumeration.WordCertificates
theorem _root_.solution {n m : ℕ}
    (source : List (FreeGroup (Fin n))) (target : List (FreeGroup (Fin m)))
    (phi : PresentedGroup (relSet source) →* PresentedGroup (relSet target))
    (hphi : Function.Surjective phi) :
    ∃ extra : List (FreeGroup (Fin n)),
      Nonempty (PresentedGroup (relSet (source ++ extra)) ≃*
        PresentedGroup (relSet target)) := by
  classical
  choose f hf using fun i : Fin n =>
    PresentedGroup.mk_surjective (relSet target) (phi (PresentedGroup.of i))
  choose pre hpre using fun j : Fin m => hphi (PresentedGroup.of j)
  choose g hg using fun j : Fin m =>
    PresentedGroup.mk_surjective (relSet source) (pre j)
  have hF := mk_lift_of_generator_images source target phi f hf
  have hfg : ∀ j, PresentedGroup.mk (relSet target) (FreeGroup.lift f (g j)) =
      PresentedGroup.of j := by
    intro j
    rw [hF, hg, hpre]
  have hfgword (w : FreeGroup (Fin m)) :
      PresentedGroup.mk (relSet target) (FreeGroup.lift f (FreeGroup.lift g w)) =
        PresentedGroup.mk (relSet target) w := by
    have h : ((PresentedGroup.mk (relSet target)).comp (FreeGroup.lift f)).comp
        (FreeGroup.lift g) = PresentedGroup.mk (relSet target) := by
      apply FreeGroup.ext_hom
      intro j
      simpa only [MonoidHom.comp_apply, FreeGroup.lift_apply_of] using hfg j
    exact DFunLike.congr_fun h w
  let lifted : List (FreeGroup (Fin n)) := target.map (FreeGroup.lift g)
  let inverse : List (FreeGroup (Fin n)) := (List.finRange n).map fun i =>
    FreeGroup.lift g (f i) * (FreeGroup.of i)⁻¹
  let extra := lifted ++ inverse
  have hlifted (r : FreeGroup (Fin m)) (hr : r ∈ target) :
      FreeGroup.lift g r ∈ source ++ extra := by
    apply List.mem_append_right
    apply List.mem_append_left
    exact List.mem_map.mpr ⟨r, hr, rfl⟩
  have hinverse (i : Fin n) : FreeGroup.lift g (f i) * (FreeGroup.of i)⁻¹ ∈
      source ++ extra := by
    apply List.mem_append_right
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨i, by simp, rfl⟩
  refine ⟨extra, exists_iso_of_maps (source ++ extra) target f g ?_ ?_ ?_ ?_⟩
  · intro r hr
    apply PresentedGroup.mk_eq_one_iff.mp
    rcases List.mem_append.mp hr with hr | hr
    · rw [hF, PresentedGroup.one_of_mem hr, phi.map_one]
    · rcases List.mem_append.mp hr with hr | hr
      · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
        rw [hfgword, PresentedGroup.one_of_mem hs]
      · obtain ⟨i, _, rfl⟩ := List.mem_map.mp hr
        rw [map_mul, map_inv, map_mul, map_inv, FreeGroup.lift_apply_of, hfgword]
        exact mul_inv_cancel _
  · intro r hr
    exact Subgroup.subset_normalClosure (hlifted r hr)
  · intro i
    exact Subgroup.subset_normalClosure (hinverse i)
  · intro j
    apply PresentedGroup.mk_eq_one_iff.mp
    rw [map_mul, map_inv, hfg]
    exact mul_inv_cancel _
end Kourovka.MetabelianEnumeration.WordCertificates
