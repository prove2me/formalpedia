-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.Paper.metabelian_iff_certificate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:41:23.88232+00:00
-- url     : https://prove2.me/submissions/8bdb9c2b-80b4-4240-8e22-a7e357f5d775

import Definitions.Def_Kourovka_Enumeration_EpimorphismEnumeration
import Definitions.Def_Metabelian16624b89_Kourovka_Paper
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableClosure_check_correct
import Theorems.Thm_Kourovka_MetabelianEnumeration_EpimorphismEnumeration_check_correct
import Theorems.Thm_Kourovka_MetabelianEnumeration_FourierMotzkin_check_correct


set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.Paper
namespace Kourovka.MetabelianEnumeration.Paper
theorem _root_.solution (p : ℕ) :
    DefinesMetabelian p ↔ ∃ c : ℕ, certificateCheck p c = true :=
  EpimorphismEnumeration.check_correct p
end Kourovka.MetabelianEnumeration.Paper
