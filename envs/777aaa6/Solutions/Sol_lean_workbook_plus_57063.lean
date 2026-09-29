-- Prove2me | solution 1 for lean_workbook_plus_57063
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:43:09.274774+00:00
-- url     : https://prove2.me/submissions/075c9db2-7286-4e20-9842-246d2086965c

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (n:ℕ) : 1 + 2^(n+1) + 4^(n+1) > 2 * (1 + 2^n + 4^n) := by
  intros
  grind
