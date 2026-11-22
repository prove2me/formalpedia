-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_EpimorphismEnumeration_check_correct
-- name    : Kourovka.MetabelianEnumeration.EpimorphismEnumeration.check_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:26:31.032921+00:00
-- url     : https://prove2.me/theorems/56f0620e-d362-4770-91f4-aa6e597ed763
-- title:
--   Epimorphism Enumeration: check correct
-- statement:
--   The main certificate equivalence, including well-formedness of the input.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Enumeration/EpimorphismEnumeration.lean#L124-L130
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Enumeration/EpimorphismEnumeration.lean#L124-L130

import Definitions.Def_Kourovka_Certificates_EpimorphismSemantics
import Definitions.Def_Kourovka_Enumeration_EnumerationCofinality
import Definitions.Def_Kourovka_Covers_ComputableCoverSemantics
import Definitions.Def_Kourovka_Covers_ComputableCoverBounds
import Definitions.Def_Kourovka_Enumeration_EpimorphismEnumeration
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableClosure_check_correct
import Theorems.Thm_Kourovka_MetabelianEnumeration_FourierMotzkin_check_correct

set_option autoImplicit true
set_option autoImplicit false
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.EpimorphismEnumeration

theorem Kourovka.MetabelianEnumeration.EpimorphismEnumeration.check_correct (p : ℕ) : DefinesMetabelian p ↔ ∃ c, check p c = true := by sorry
