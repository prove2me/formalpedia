-- Prove2me | solution 1 for lean_workbook_plus_13963
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:39:09.900987+00:00
-- url     : https://prove2.me/submissions/06e2c9a7-0d55-4b0e-bba1-06a2473194f3

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 150000



theorem solution (f : ℕ → ℕ → ℝ)
  (h₀ : ∀ m, f m 0 = m)
  (h₁ : ∀ m, f 0 m = m)
  (h₂ : ∀ m, f m m = 1 / 2 + f m (m - 1))
  (h₃ : ∀ m n, m ≠ n → f m n = n / (m + n) * (f m (n - 1) + if n > m then 1 else 0) + m / (m + n) * (f (m - 1) n + if m > n then 1 else 0)) :
  f 3 3 = 41 / 10 := by
  have hd1 := h₂ 1
  have hd2 := h₂ 2
  have hd3 := h₂ 3
  clear h₂
  grind
