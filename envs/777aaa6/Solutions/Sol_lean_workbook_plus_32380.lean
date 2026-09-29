-- Prove2me | solution 1 for lean_workbook_plus_32380
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:58:44.104838+00:00
-- url     : https://prove2.me/submissions/7d011756-277f-42ee-bf89-9a66387df32f

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution {x y z : ℝ} (hx : x = 4) (hy : y = 4) (hz : z = 2 / 3) : (4 - x ^ 2) * (4 - y ^ 2) * (4 - z ^ 2) = 512 := by
  intros
  grind
