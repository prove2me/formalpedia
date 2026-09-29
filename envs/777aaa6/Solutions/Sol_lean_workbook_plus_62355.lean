-- Prove2me | solution 1 for lean_workbook_plus_62355
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:40:23.308174+00:00
-- url     : https://prove2.me/submissions/cfaa9524-17d5-4fc0-8956-7a2fb3372349

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (m n : ℕ)
  (h₀ : 0 < m ∧ 0 < n)
  (h₁ : 2 * m < 2^n) :
  m ≤ 2^(n - 1) - 1 := by
  have hn : n=n-1+1 := by omega
  have hp : 2^n=2*2^(n-1) := by
    conv_lhs => rw [hn]
    rw [pow_succ]
    ring
  rw [hp] at h₁
  omega
