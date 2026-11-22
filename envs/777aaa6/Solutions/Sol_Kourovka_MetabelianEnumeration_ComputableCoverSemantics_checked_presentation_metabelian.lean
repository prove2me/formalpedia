-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableCoverSemantics.checked_presentation_metabelian
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:21:24.39287+00:00
-- url     : https://prove2.me/submissions/c5c93764-845e-4cda-a1ea-bd406fc11de2

import Definitions.Def_Kourovka_Covers_ComputableCoverWords
import Definitions.Def_Kourovka_Covers_ComputableCoverSemantics
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverSemantics_code_generators
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverSemantics_code_realizes
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverData_check_sound
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_realizationHom_surjective
import Theorems.Thm_Kourovka_MetabelianEnumeration_metabelian_surjective


set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCoverSemantics
open ComputableCoverData ComputableCoverWords FiniteCover
variable {G : Type*} [Group G]
namespace Kourovka.MetabelianEnumeration.ComputableCoverSemantics
theorem _root_.solution (data : DatumCode) (r : ℕ)
    (hcheck : ComputableCoverData.check data r = true) :
    Metabelian (MetabelianEnumeration.GroupOf (presentation data (radius data r))) := by
  exact metabelian_surjective
    (realizationHom (decode data) (radius data r) _ _ (code_realizes data (radius data r)))
    (realizationHom_surjective (decode data) (radius data r) _ _
      (code_realizes data (radius data r)) (code_generators data (radius data r)))
    (ComputableCoverData.check_sound data r hcheck)
end Kourovka.MetabelianEnumeration.ComputableCoverSemantics
