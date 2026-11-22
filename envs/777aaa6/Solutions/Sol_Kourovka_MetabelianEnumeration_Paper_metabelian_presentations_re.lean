-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.Paper.metabelian_presentations_re
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:43:44.402147+00:00
-- url     : https://prove2.me/submissions/b258ce59-b417-40e6-a968-0bfc096d39eb

import Definitions.Def_Kourovka_Enumeration_EpimorphismEnumeration
import Definitions.Def_Metabelian16624b89_Kourovka_Paper
import Theorems.Thm_Kourovka_MetabelianEnumeration_EpimorphismEnumeration_kourovka_17_124_via_epimorphisms


set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.Paper
namespace Kourovka.MetabelianEnumeration.Paper
theorem _root_.solution : REPred DefinesMetabelian :=
  EpimorphismEnumeration.kourovka_17_124_via_epimorphisms
end Kourovka.MetabelianEnumeration.Paper
