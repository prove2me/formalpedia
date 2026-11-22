-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.Paper.certificateCheck_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:32:34.760798+00:00
-- url     : https://prove2.me/submissions/c499a536-f59e-44ab-b22e-fb7c21cc2b7c

import Definitions.Def_Kourovka_Enumeration_EpimorphismEnumeration
import Definitions.Def_Metabelian16624b89_Kourovka_Paper
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableClosure_check_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverData_check_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableEnumeration_check_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableFourierMotzkin_check_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_EpimorphismEnumeration_check_primrec


set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.Paper
namespace Kourovka.MetabelianEnumeration.Paper
theorem _root_.solution : Primrec₂ certificateCheck :=
  EpimorphismEnumeration.check_primrec
end Kourovka.MetabelianEnumeration.Paper
