-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_relators_finite
-- name    : Kourovka.MetabelianEnumeration.FiniteCover.relators_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:02:59.956617+00:00
-- url     : https://prove2.me/theorems/4a84969f-08d8-4f47-a387-80407a940205
-- title:
--   Finite Cover: relators finite
-- statement:
--   The Finite Cover construction uses the relators finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/FiniteCover.lean#L139-L140
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/FiniteCover.lean#L139-L140

import Definitions.Def_Kourovka_Polyhedral_ConeMargin
import Definitions.Def_Kourovka_Presentations_FiniteQuotient
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Lex
import Definitions.Def_Kourovka_Covers_FiniteCover
set_option autoImplicit true
attribute [-instance] instConditionallyCompleteLinearOrder
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover

theorem Kourovka.MetabelianEnumeration.FiniteCover.relators_finite {k a : ℕ} (data : Datum k a) (radius : ℕ) :
    (WordCertificates.relSet (relators data radius)).Finite := by sorry
