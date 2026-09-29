-- Prove2me | solution 1 for lean_workbook_plus_45519
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T21:57:13.250909+00:00
-- url     : https://prove2.me/submissions/9fb4e12c-50bf-4851-94db-fc55aae306fe

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (n : ℤ) : n^7 ≡ n [ZMOD 7] := by
  exact Int.ModEq.pow_prime_eq_self (by decide : Nat.Prime 7) n
