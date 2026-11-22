-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableCoverSemantics.presentation_epimorphism
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:18:23.379604+00:00
-- url     : https://prove2.me/submissions/8b2840bc-e767-4d25-9954-2c30a77e755f

import Definitions.Def_Kourovka_Covers_ComputableCoverWords
import Definitions.Def_Kourovka_Covers_ComputableCoverSemantics
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverSemantics_codeRealizationHom_surjective
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_group_generators
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_group_realizes


set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCoverSemantics
open ComputableCoverData ComputableCoverWords FiniteCover
variable {G : Type*} [Group G]
namespace Kourovka.MetabelianEnumeration.ComputableCoverSemantics
theorem _root_.solution (data : DatumCode) (R : ℕ) :
    ∃ f : MetabelianEnumeration.GroupOf (presentation data R) →*
      FiniteCover.GroupOf (decode data) R, Function.Surjective f := by
  exact ⟨codeRealizationHom data R _ _ (FiniteCover.group_realizes (decode data) R),
    codeRealizationHom_surjective data R _ _ (FiniteCover.group_realizes (decode data) R)
      (FiniteCover.group_generators (decode data) R)⟩
end Kourovka.MetabelianEnumeration.ComputableCoverSemantics
