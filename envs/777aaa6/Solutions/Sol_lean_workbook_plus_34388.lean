-- Prove2me | solution 1 for lean_workbook_plus_34388
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:17:59.057717+00:00
-- url     : https://prove2.me/submissions/5abf8aa2-ba32-4527-b34e-9c7a74952d4c

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (n : ℕ) : n = 74892^359 * 6379^207 * 9538^179 * 3756^723 → n % 5 = 4 := by
  intros
  grind
