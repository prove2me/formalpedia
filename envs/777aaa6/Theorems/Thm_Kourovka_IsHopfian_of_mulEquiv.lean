-- Prove2me | Theorems.Thm_Kourovka_IsHopfian_of_mulEquiv
-- name    : Kourovka.IsHopfian.of_mulEquiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:36:16.381105+00:00
-- url     : https://prove2.me/theorems/62ca1d2c-8813-4304-8bc1-63a379fd2fd3
-- title:
--   Is Hopfian: of mul Equiv
-- statement:
--   The Is Hopfian construction uses the of mul Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/Hopfian.lean#L22-L31
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/Hopfian.lean#L22-L31

import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.Finiteness
import Mathlib.GroupTheory.Solvable
import Mathlib.RingTheory.Noetherian.Orzech
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Data.Fintype.Card
import Definitions.Def_Kourovka_Hopfian
set_option autoImplicit true
open Kourovka
variable {G H : Type*} [Group G] [Group H]

theorem Kourovka.IsHopfian.of_mulEquiv (hG : IsHopfian G) (e : G ≃* H) : IsHopfian H := by sorry
