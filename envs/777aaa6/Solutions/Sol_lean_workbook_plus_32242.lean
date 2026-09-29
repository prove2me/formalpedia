-- Prove2me | solution 1 for lean_workbook_plus_32242
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:35:25.967066+00:00
-- url     : https://prove2.me/submissions/1f0f7197-05cc-44db-aeec-884fb8f119ea

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (z1 z2 z3 : ℂ) (hz1 : z1 ≠ z2) (hz2 : z1 ≠ z3) (hz3 : z2 ≠ z3) (h1 : z1 ^ 3 = z2 ^ 3) (h2 : z1 ^ 3 = z3 ^ 3) (h3 : z2 ^ 3 = z3 ^ 3) : z1 + z2 + z3 = 0 := by
  intros
  grind
