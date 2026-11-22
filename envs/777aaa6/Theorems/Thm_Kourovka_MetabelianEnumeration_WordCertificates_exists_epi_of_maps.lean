-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_WordCertificates_exists_epi_of_maps
-- name    : Kourovka.MetabelianEnumeration.WordCertificates.exists_epi_of_maps
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:04:13.779375+00:00
-- url     : https://prove2.me/theorems/449d29a9-5fee-4a27-bef2-5303e14b6d3f
-- title:
--   Word Certificates: exists epi of maps
-- statement:
--   Source-relator identities and one preimage for each target generator
--   suffice for a surjective homomorphism. No reverse relator identities occur.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/EpimorphismSemantics.lean#L18-L34
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/EpimorphismSemantics.lean#L18-L34

import Definitions.Def_Kourovka_Certificates_ComputableEpimorphism
import Definitions.Def_Kourovka_Certificates_IsomorphismSemantics
import Definitions.Def_Kourovka_Certificates_EpimorphismSemantics
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.WordCertificates

theorem Kourovka.MetabelianEnumeration.WordCertificates.exists_epi_of_maps {n m : ℕ} (source : List (FreeGroup (Fin n)))
    (target : List (FreeGroup (Fin m))) (f : Fin n → FreeGroup (Fin m))
    (g : Fin m → FreeGroup (Fin n))
    (hf : ∀ r ∈ source, FreeGroup.lift f r ∈ Subgroup.normalClosure (relSet target))
    (hfg : ∀ i, FreeGroup.lift f (g i) * (FreeGroup.of i)⁻¹ ∈
      Subgroup.normalClosure (relSet target)) :
    ∃ F : PresentedGroup (relSet source) →* PresentedGroup (relSet target),
      Function.Surjective F := by sorry
