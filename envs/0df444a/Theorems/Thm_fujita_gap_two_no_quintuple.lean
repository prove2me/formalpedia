-- Prove2me | Theorems.Thm_fujita_gap_two_no_quintuple
-- name    : fujita_gap_two_no_quintuple
-- status  : Open
-- author  : @junyihjy
-- created : 2026-09-28T00:38:59.193378+00:00
-- url     : https://prove2.me/theorems/5a227798-0fa4-4059-9970-84a72c388503
-- title:
--   Fujita gap-two: no distance-two pair extends to a quintuple
-- statement:
--   Y. Fujita ("The extensibility of Diophantine pairs {k-1,k+1}", J. Number Theory 128 (2008), 322-353): for k >= 2, the Diophantine pair {k-1, k+1} cannot be extended to a Diophantine quintuple. The proof uses simultaneous Pell equations reduced to linear forms in logarithms (Baker's method); no elementary proof is known. Deep input behind diophantine_no_consecutive_gap_two: with the elementary gap-one exclusion it yields b - a >= 3 for any Diophantine quintuple a < b < c < d < e.
-- source:
--   Y. Fujita, J. Number Theory 128 (2008), 322-353

import Definitions.Def_diophantine_descent
set_option autoImplicit false
open DiophantineDescent

theorem fujita_gap_two_no_quintuple (f : Fin 5 → Nat)
    (hq : Quintuple f) (ho : Ordered f) (h2 : f 1 - f 0 = 2) : False := by sorry
