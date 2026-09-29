-- Prove2me | solution 1 for lean_workbook_plus_53377
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:17:31.928761+00:00
-- url     : https://prove2.me/submissions/5aa9407e-420b-4e62-9571-4197139edf9c

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ∀ n : ℤ, n ≡ 1 [ZMOD 3] → n ^ 2 + 2 ≡ 0 [ZMOD 3] := by
  intro n hn
  have hp := (hn.pow 2).add_right 2
  exact hp.trans (by norm_num [Int.ModEq])
