-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.WordCertificates.exists_epi_of_maps
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:04:16.79981+00:00
-- url     : https://prove2.me/submissions/b2acf916-ca82-4a43-9ebf-8d52af3f57be

import Definitions.Def_Kourovka_Certificates_ComputableEpimorphism
import Definitions.Def_Kourovka_Certificates_IsomorphismSemantics
import Definitions.Def_Kourovka_Certificates_EpimorphismSemantics
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIsomorphism_encodeImages_length
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIsomorphism_interpret_encodeImages_getD
import Theorems.Thm_Kourovka_MetabelianEnumeration_WordCertificates_descend_mk
attribute [local simp] Kourovka.MetabelianEnumeration.ComputableIsomorphism.encodeImages_length
attribute [local simp] Kourovka.MetabelianEnumeration.ComputableIsomorphism.interpret_encodeImages_getD



set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.WordCertificates
namespace Kourovka.MetabelianEnumeration.WordCertificates
theorem _root_.solution {n m : ℕ} (source : List (FreeGroup (Fin n)))
    (target : List (FreeGroup (Fin m))) (f : Fin n → FreeGroup (Fin m))
    (g : Fin m → FreeGroup (Fin n))
    (hf : ∀ r ∈ source, FreeGroup.lift f r ∈ Subgroup.normalClosure (relSet target))
    (hfg : ∀ i, FreeGroup.lift f (g i) * (FreeGroup.of i)⁻¹ ∈
      Subgroup.normalClosure (relSet target)) :
    ∃ F : PresentedGroup (relSet source) →* PresentedGroup (relSet target),
      Function.Surjective F := by
  let F := descend source target f hf
  refine ⟨F, ?_⟩
  intro y
  apply PresentedGroup.generated_by (relSet target) F.range
  · intro i
    refine ⟨PresentedGroup.mk (relSet source) (g i), ?_⟩
    rw [show F = descend source target f hf from rfl, descend_mk]
    have h := PresentedGroup.mk_eq_one_iff.mpr (hfg i)
    simpa only [map_mul, map_inv, mul_inv_eq_one, PresentedGroup.of] using h
end Kourovka.MetabelianEnumeration.WordCertificates
