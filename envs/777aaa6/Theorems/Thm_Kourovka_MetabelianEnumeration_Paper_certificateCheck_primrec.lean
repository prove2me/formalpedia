-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_Paper_certificateCheck_primrec
-- name    : Kourovka.MetabelianEnumeration.Paper.certificateCheck_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:28:10.628096+00:00
-- url     : https://prove2.me/theorems/33648af4-c70a-4f43-9f65-8865ac99bd77
-- title:
--   Paper: certificate Check primrec
-- statement:
--   Checking a proposed certificate is primitive recursive in both inputs.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Paper.lean#L35-L36
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Paper.lean#L35-L36

import Definitions.Def_Kourovka_Enumeration_EpimorphismEnumeration
import Definitions.Def_Metabelian16624b89_Kourovka_Paper
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.Paper

theorem Kourovka.MetabelianEnumeration.Paper.certificateCheck_primrec : Primrec₂ certificateCheck := by sorry
