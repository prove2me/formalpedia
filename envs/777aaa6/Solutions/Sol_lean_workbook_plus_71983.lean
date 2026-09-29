-- Prove2me | solution 1 for lean_workbook_plus_71983
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:53:44.096167+00:00
-- url     : https://prove2.me/submissions/fc69ae4b-5e24-45c1-ab18-abe64d7ea934

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (p q : ℝ) : 4 * q < 4 * p - 1 ↔ q < p - 1 / 4 := by
  intros
  field_simp at * <;> ring
