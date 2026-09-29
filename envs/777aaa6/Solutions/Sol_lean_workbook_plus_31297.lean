-- Prove2me | solution 1 for lean_workbook_plus_31297
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T21:47:00.64747+00:00
-- url     : https://prove2.me/submissions/f8dc1ddb-4310-48c3-b141-76bce5a8429e

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Int.ModEq

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (a b : ℤ) (p : ℕ) (hp : p.Prime) (h : a^2 + a*b + b^2 ≡ 0 [ZMOD p]) : (a + b)^2 ≡ a * b [ZMOD p] := by
  clear hp
  convert h.add (Int.ModEq.refl (a * b)) using 1 <;> ring
