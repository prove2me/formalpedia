-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.WordCertificates.exists_iso_of_maps
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:01:02.055169+00:00
-- url     : https://prove2.me/submissions/108da994-f197-47fd-9102-be2f680e8e6f

import Definitions.Def_Kourovka_Certificates_WordCertificates
import Definitions.Def_Kourovka_Certificates_PresentationIsomorphism
import Theorems.Thm_Kourovka_MetabelianEnumeration_WordCertificates_descend_of
import Theorems.Thm_Kourovka_MetabelianEnumeration_WordCertificates_descend_mk

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.WordCertificates
namespace Kourovka.MetabelianEnumeration.WordCertificates
theorem _root_.solution {n m : ℕ} (source : List (FreeGroup (Fin n)))
    (target : List (FreeGroup (Fin m))) (f : Fin n → FreeGroup (Fin m))
    (g : Fin m → FreeGroup (Fin n))
    (hf : ∀ r ∈ source, FreeGroup.lift f r ∈ Subgroup.normalClosure (relSet target))
    (hg : ∀ r ∈ target, FreeGroup.lift g r ∈ Subgroup.normalClosure (relSet source))
    (hgf : ∀ i, FreeGroup.lift g (f i) * (FreeGroup.of i)⁻¹ ∈
      Subgroup.normalClosure (relSet source))
    (hfg : ∀ i, FreeGroup.lift f (g i) * (FreeGroup.of i)⁻¹ ∈
      Subgroup.normalClosure (relSet target)) :
    Nonempty (PresentedGroup (relSet source) ≃* PresentedGroup (relSet target)) := by
  let F := descend source target f hf
  let G := descend target source g hg
  have hGF : G.comp F = MonoidHom.id _ := by
    apply PresentedGroup.ext
    intro i
    change G (F (PresentedGroup.of i)) = PresentedGroup.of i
    rw [descend_of, descend_mk]
    have h := PresentedGroup.mk_eq_one_iff.mpr (hgf i)
    simpa only [map_mul, map_inv, mul_inv_eq_one] using h
  have hFG : F.comp G = MonoidHom.id _ := by
    apply PresentedGroup.ext
    intro i
    change F (G (PresentedGroup.of i)) = PresentedGroup.of i
    rw [descend_of, descend_mk]
    have h := PresentedGroup.mk_eq_one_iff.mpr (hfg i)
    simpa only [map_mul, map_inv, mul_inv_eq_one] using h
  exact ⟨F.toMulEquiv G hGF hFG⟩
end Kourovka.MetabelianEnumeration.WordCertificates
