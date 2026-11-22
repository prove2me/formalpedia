-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_Paper_metabelian_presentations_re
-- name    : Kourovka.MetabelianEnumeration.Paper.metabelian_presentations_re
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:28:03.026079+00:00
-- url     : https://prove2.me/theorems/938d7988-70c0-4ac6-8c36-e31a8bcaf243
-- title:
--   Paper: metabelian presentations re
-- statement:
--   Ordinary finite presentations of metabelian groups are recursively enumerable.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Paper.lean#L45-L46
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Paper.lean#L45-L46

import Definitions.Def_Kourovka_Enumeration_EpimorphismEnumeration
import Definitions.Def_Metabelian16624b89_Kourovka_Paper
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.Paper

theorem Kourovka.MetabelianEnumeration.Paper.metabelian_presentations_re : REPred DefinesMetabelian := by sorry
