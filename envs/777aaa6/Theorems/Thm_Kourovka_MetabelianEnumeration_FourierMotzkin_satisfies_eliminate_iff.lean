-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_FourierMotzkin_satisfies_eliminate_iff
-- name    : Kourovka.MetabelianEnumeration.FourierMotzkin.satisfies_eliminate_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:52:04.924807+00:00
-- url     : https://prove2.me/theorems/2d6012c2-056e-4050-877e-48a9fdfb2574
-- title:
--   Fourier Motzkin: satisfies eliminate iff
-- statement:
--   The Fourier Motzkin construction uses the satisfies eliminate iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/FourierMotzkin.lean#L120-L148
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/FourierMotzkin.lean#L120-L148

import Definitions.Def_Kourovka_Presentations_Presentations
import Definitions.Def_Kourovka_Polyhedral_FourierMotzkin
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FourierMotzkin

theorem Kourovka.MetabelianEnumeration.FourierMotzkin.satisfies_eliminate_iff {n : ℕ} (rows : List (Row (n + 1)))
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (x : Fin n → K) :
    Satisfies (eliminate rows) x ↔
      (∀ r ∈ rows, r.head = 0 → r.tail.eval x ≤ 0) ∧
      (∀ l ∈ rows, l.head < 0 → ∀ u ∈ rows, 0 < u.head →
        (l.combine u).eval x ≤ 0) := by sorry
