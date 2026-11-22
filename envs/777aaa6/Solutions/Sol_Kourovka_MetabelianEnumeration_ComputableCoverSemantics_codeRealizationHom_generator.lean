-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableCoverSemantics.codeRealizationHom_generator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:15:54.772844+00:00
-- url     : https://prove2.me/submissions/1255f995-ca10-47a3-8187-325ea5a6d017

import Definitions.Def_Kourovka_Covers_ComputableCoverWords
import Definitions.Def_Kourovka_Covers_ComputableCoverSemantics

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCoverSemantics
open ComputableCoverData ComputableCoverWords FiniteCover
variable {G : Type*} [Group G]
namespace Kourovka.MetabelianEnumeration.ComputableCoverSemantics
theorem _root_.solution (data : DatumCode) (R : ℕ)
    (t : Fin (dimension data) → G) (A : Fin (alphabet data) → G)
    (h : Realizes (decode data) R t A) (i : Fin (dimension data + alphabet data)) :
    codeRealizationHom data R t A h (PresentedGroup.of i) = generatorAssignment t A i :=
  PresentedGroup.toGroup.of _
end Kourovka.MetabelianEnumeration.ComputableCoverSemantics
