-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.WordCertificates.code_metabelian_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:17:31.945249+00:00
-- url     : https://prove2.me/submissions/19d607fc-ec02-4a18-81e5-2b2fffc4397e

import Definitions.Def_Kourovka_Certificates_PresentationIsomorphism
import Definitions.Def_Kourovka_Presentations_RelatorCodes
import Theorems.Thm_Kourovka_MetabelianEnumeration_metabelian_surjective


set_option autoImplicit true
attribute [refl] MulEquiv.refl
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.WordCertificates
namespace Kourovka.MetabelianEnumeration.WordCertificates
theorem _root_.solution {n : ℕ} (rels : List (FreeGroup (Fin n))) :
    Metabelian (Kourovka.MetabelianEnumeration.GroupOf (encodeRelators rels)) ↔
      Metabelian (PresentedGroup (relSet rels)) := by
  constructor
  · exact metabelian_surjective (codeGroupEquiv rels).toMonoidHom (codeGroupEquiv rels).surjective
  · exact metabelian_surjective (codeGroupEquiv rels).symm.toMonoidHom
      (codeGroupEquiv rels).symm.surjective
end Kourovka.MetabelianEnumeration.WordCertificates
