-- Prove2me | solution 1 for lean_workbook_plus_9866
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:12:46.426431+00:00
-- url     : https://prove2.me/submissions/0db99989-e658-477f-afb2-1787ea26240a

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (z : ℂ)
  (h₀ : 8 * z^3 - 6 * z + 1 = 0) :
  4 * z^3 - 3 * z = - 1 / 2 := by
  intros
  norm_num at * <;> first | omega | nlinarith | grind
