-- Prove2me | solution 1 for BookSixth.cycSucc_ne_self
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-16T16:36:08.67089+00:00
-- url     : https://prove2.me/submissions/7d08f629-4738-4d17-9b93-eb7cf69b8eb0

import Mathlib
import Definitions.Def_BookSixthRandomGraph

set_option autoImplicit false

theorem solution (l : Nat) (hl0 : 0 < l) (hl1 : 1 < l) :
    forall i : Fin l, Ne (BookSixth.cycSucc hl0 i) i := by
  intro i hcon
  cases i with
  | mk m h =>
    have h2 : (m + 1) % l = m := congrArg Fin.val hcon
    have hcase := lt_or_ge (m + 1) l
    rcases hcase with hlt1 | hge
    next =>
      rw [Nat.mod_eq_of_lt hlt1] at h2
      omega
    next =>
      have h3 : m + 1 = l := by omega
      rw [h3, Nat.mod_self] at h2
      have hle1 : l = 1 := by rw [← h3, ← h2]
      omega
