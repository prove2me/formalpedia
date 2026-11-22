-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.decode_encode_presentation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:16:45.688764+00:00
-- url     : https://prove2.me/submissions/f794a06d-820e-4b83-b67d-e2863b1a0b87

import Definitions.Def_Kourovka_Computability_Enumeration
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.Commutator.Basic
import Definitions.Def_Kourovka_Presentations_Presentations

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration
namespace Kourovka.MetabelianEnumeration
theorem _root_.solution (p : PresentationCode) :
    decodePresentation (Encodable.encode p) = p := by simp [decodePresentation]
end Kourovka.MetabelianEnumeration
