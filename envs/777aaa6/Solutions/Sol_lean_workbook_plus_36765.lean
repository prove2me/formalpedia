-- Prove2me | solution 1 for lean_workbook_plus_36765
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:00:02.838168+00:00
-- url     : https://prove2.me/submissions/e85ffa3f-89ce-441d-b9e7-08fe5549f015

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (n : ℕ) (x : ℝ) (hx: x < 1/n) : 1 - n * x > 0 := by
  by_cases hn : n=0
  · subst n
    norm_num
  have hp : (0:ℝ)<n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hh := (lt_div_iff₀ hp).mp hx
  nlinarith only [hh]
