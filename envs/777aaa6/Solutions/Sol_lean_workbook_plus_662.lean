-- Prove2me | solution 1 for lean_workbook_plus_662
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:57:13.888374+00:00
-- url     : https://prove2.me/submissions/4140c458-ef27-47cd-a223-f40174595f9b

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution : ∀ a b : ℤ, Odd a ∧ Odd b → Even (a^2 + b^2 + 26) ∧ Odd (5 * a * b) := by
  intro a b h
  rcases h with ⟨ha,hb⟩
  constructor
  · exact ((show Odd (a^2) from ha.pow).add_odd (show Odd (b^2) from hb.pow)).add (by norm_num : Even (26:ℤ))
  · exact ((by norm_num : Odd (5:ℤ)).mul ha).mul hb
