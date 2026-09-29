-- Prove2me | solution 1 for lean_workbook_plus_30638
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:40:13.038568+00:00
-- url     : https://prove2.me/submissions/26fcde6c-1085-4062-93c0-a743b352e942

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℤ) : 3*x*(2*x-1) - 4*(2*x-1) = (3*x-4)*(2*x-1) := by
  (intros; linarith)
