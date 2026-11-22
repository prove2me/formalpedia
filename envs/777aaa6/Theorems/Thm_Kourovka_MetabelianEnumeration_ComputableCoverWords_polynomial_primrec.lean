-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverWords_polynomial_primrec
-- name    : Kourovka.MetabelianEnumeration.ComputableCoverWords.polynomial_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:56:56.172404+00:00
-- url     : https://prove2.me/theorems/4221aab9-ff7e-4b55-bd13-bc946027aec4
-- title:
--   Computable Cover Words: polynomial primrec
-- statement:
--   The Computable Cover Words construction uses the polynomial primrec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableCoverWords.lean#L99-L110
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableCoverWords.lean#L99-L110

import Definitions.Def_Kourovka_Covers_ComputableLatticeBall
import Definitions.Def_Kourovka_Presentations_RelatorCodes
import Definitions.Def_Kourovka_Covers_ComputableCoverWords
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCoverWords
open ComputableCoverData

theorem Kourovka.MetabelianEnumeration.ComputableCoverWords.polynomial_primrec : Primrec (fun p : (ℕ × WordGroup) × PolynomialCode =>
    polynomial p.1.1 p.1.2 p.2) := by sorry
