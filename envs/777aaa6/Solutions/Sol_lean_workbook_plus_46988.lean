-- Prove2me | solution 1 for lean_workbook_plus_46988
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:32:23.511354+00:00
-- url     : https://prove2.me/submissions/6aac2b03-f575-4e5b-9c6a-be9634c1c749

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ∀ n : ℤ, n ≡ 2 [ZMOD 3] → n ^ 2 + 2 ≡ 0 [ZMOD 3] := by
  intro n h
  have hp := (h.pow 2).add (Int.ModEq.refl (2 : ℤ))
  exact hp.trans (by norm_num [Int.ModEq])
