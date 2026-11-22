-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableEnumeration_check_primrec
-- name    : Kourovka.MetabelianEnumeration.ComputableEnumeration.check_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:15:39.124222+00:00
-- url     : https://prove2.me/theorems/f0b93323-6121-477c-a0f0-8f6cf5f5199c
-- title:
--   Computable Enumeration: check primrec
-- statement:
--   The combined finite checker is primitive recursive, including dimension
--   decoding, cone margins, cover relators, and the isomorphism equations.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Enumeration/ComputableEnumeration.lean#L84-L86
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Enumeration/ComputableEnumeration.lean#L84-L86

import Definitions.Def_Kourovka_Covers_ComputableCoverWords
import Definitions.Def_Kourovka_Presentations_QuotientCodes
import Definitions.Def_Kourovka_Enumeration_ComputableEnumeration
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableClosure_check_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverData_check_primrec
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableFourierMotzkin_check_primrec

set_option autoImplicit true
set_option autoImplicit false
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableEnumeration

theorem Kourovka.MetabelianEnumeration.ComputableEnumeration.check_primrec : Primrec₂ check := by sorry
