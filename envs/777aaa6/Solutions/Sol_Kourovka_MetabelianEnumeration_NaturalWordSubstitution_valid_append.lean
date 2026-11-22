-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.NaturalWordSubstitution.valid_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:51:25.551494+00:00
-- url     : https://prove2.me/submissions/566b9a1a-5475-4db4-9a05-970f4372bb6f

import Definitions.Def_Kourovka_Computability_ComputablePresentations
import Definitions.Def_Kourovka_Presentations_RelatorCodes
import Mathlib.Data.List.GetD
import Definitions.Def_Kourovka_Certificates_NaturalWordSubstitution

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.NaturalWordSubstitution
open ComputableWords ComputablePresentations
namespace Kourovka.MetabelianEnumeration.NaturalWordSubstitution
theorem _root_.solution {n : ℕ} {u v : Word} (hu : ValidWord n u) (hv : ValidWord n v) :
    ValidWord n (u ++ v) := by
  intro z hz
  exact (List.mem_append.mp hz).elim (hu z) (hv z)
end Kourovka.MetabelianEnumeration.NaturalWordSubstitution
