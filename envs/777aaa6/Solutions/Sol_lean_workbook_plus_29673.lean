-- Prove2me | solution 1 for lean_workbook_plus_29673
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:18:59.19406+00:00
-- url     : https://prove2.me/submissions/cd1618df-4609-461e-8904-6f15c304b455

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (e : ℤ → ℝ)
  (h₀ : ∀ n, e (-n) = e n)
  (h₁ : e 0 = (e (-1) + e 1) / 2 + 1)
  (h₂ : e 1 = 7 / 8 * e 0 + 7) :
  e 0 = 64 := by
  intros
  norm_num at * <;> first | omega | nlinarith | grind
