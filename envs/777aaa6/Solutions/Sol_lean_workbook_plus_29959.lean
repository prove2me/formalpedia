-- Prove2me | solution 1 for lean_workbook_plus_29959
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:06:53.086531+00:00
-- url     : https://prove2.me/submissions/7860ba17-567a-48d5-9269-187e70853021

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ∀ x : ℝ, (Int.floor x - 2 * Int.floor (x / 2)) < 2 := by
  intro x
  have h1 := Int.floor_le x
  have h2 := Int.lt_floor_add_one (x/2)
  have he : ((Int.floor x-2*Int.floor (x/2):ℤ):ℝ)<2 := by push_cast; linarith
  exact_mod_cast he
