-- Prove2me | solution 1 for lean_workbook_plus_15059
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T21:22:01.716366+00:00
-- url     : https://prove2.me/submissions/e394cc68-b1db-4ba1-9846-1b853d6114df

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution : ∀ P ∈ Set.Icc (3 - 2 * Real.sqrt 2) 4, 2 * P ^ 3 - 10 * P ^ 2 + 9 * P - 4 ≤ 0 := by
  rintro P ⟨hlo, hhi⟩
  have hq : 0 ≤ 2*P^2-2*P+1 := by nlinarith [sq_nonneg (P-1/2)]
  have hp := mul_nonpos_of_nonpos_of_nonneg (show P-4 ≤ 0 by linarith) hq
  nlinarith
