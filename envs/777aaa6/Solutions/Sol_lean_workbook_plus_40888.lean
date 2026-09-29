-- Prove2me | solution 1 for lean_workbook_plus_40888
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:48:03.941015+00:00
-- url     : https://prove2.me/submissions/6c5fae4a-ab82-4d1b-a10a-497ff9446123

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (f : ℕ → ℕ) (n : ℕ) (h₁ : f 1 = 1) (h₂ : ∀ n, f (n + 1) = f n + 1) : f n = f 1 + n - 1 := by
  have hz : f 0=0 := by have h := h₂ 0; norm_num at h; omega
  have he (k : ℕ) : f k=k := by
    induction k with
    | zero => exact hz
    | succ k ih => rw [h₂,ih]
  rw [he,h₁]
  omega
