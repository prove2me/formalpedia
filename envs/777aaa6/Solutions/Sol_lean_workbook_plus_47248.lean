-- Prove2me | solution 1 for lean_workbook_plus_47248
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:04:22.568942+00:00
-- url     : https://prove2.me/submissions/5cbe4e0e-a113-4414-a7ab-7f11e47002db

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ∀ n : ℕ, (8^n - 1) / (2^(n + 3) - 1) = (2^(3 * n) - 1) / (2^(n + 3) - 1) := by
  intro n
  have he : (8:ℕ)^n=2^(3*n) := by rw [pow_mul]; norm_num
  rw [he]
