-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_WordCertificates_exists_iso_of_maps
-- name    : Kourovka.MetabelianEnumeration.WordCertificates.exists_iso_of_maps
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:45:13.659457+00:00
-- url     : https://prove2.me/theorems/ea0fcd92-041a-4470-95d2-c4d6a5bbbd0c
-- title:
--   Word Certificates: exists iso of maps
-- statement:
--   The Word Certificates construction uses the exists iso of maps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/PresentationIsomorphism.lean#L82-L108
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/PresentationIsomorphism.lean#L82-L108

import Definitions.Def_Kourovka_Certificates_WordCertificates
import Definitions.Def_Kourovka_Certificates_PresentationIsomorphism
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.WordCertificates

theorem Kourovka.MetabelianEnumeration.WordCertificates.exists_iso_of_maps {n m : ℕ} (source : List (FreeGroup (Fin n)))
    (target : List (FreeGroup (Fin m))) (f : Fin n → FreeGroup (Fin m))
    (g : Fin m → FreeGroup (Fin n))
    (hf : ∀ r ∈ source, FreeGroup.lift f r ∈ Subgroup.normalClosure (relSet target))
    (hg : ∀ r ∈ target, FreeGroup.lift g r ∈ Subgroup.normalClosure (relSet source))
    (hgf : ∀ i, FreeGroup.lift g (f i) * (FreeGroup.of i)⁻¹ ∈
      Subgroup.normalClosure (relSet source))
    (hfg : ∀ i, FreeGroup.lift f (g i) * (FreeGroup.of i)⁻¹ ∈
      Subgroup.normalClosure (relSet target)) :
    Nonempty (PresentedGroup (relSet source) ≃* PresentedGroup (relSet target)) := by sorry
