-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_Paper_metabelian_iff_certificate
-- name    : Kourovka.MetabelianEnumeration.Paper.metabelian_iff_certificate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:28:25.849172+00:00
-- url     : https://prove2.me/theorems/9a185419-9e00-4ab0-8af2-1c9b780af9df
-- title:
--   Paper: metabelian iff certificate
-- statement:
--   Theorem 1.1: a valid presentation defines a metabelian group exactly when
--   some finite certificate is accepted.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Paper.lean#L40-L42
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Paper.lean#L40-L42

import Definitions.Def_Kourovka_Enumeration_EpimorphismEnumeration
import Definitions.Def_Metabelian16624b89_Kourovka_Paper
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.Paper

theorem Kourovka.MetabelianEnumeration.Paper.metabelian_iff_certificate (p : ℕ) :
    DefinesMetabelian p ↔ ∃ c : ℕ, certificateCheck p c = true := by sorry
