-- Prove2me | solution 1 for lean_workbook_plus_12280
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T21:57:07.174865+00:00
-- url     : https://prove2.me/submissions/8d5779cc-2186-431d-9c2c-5c006cecd873

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (p t r : ℝ) (h₀ : 0 < p ∧ 0 < t) (h₁ : p < t) (h₂ : 0 < r) : p / (t - p) < r ↔ p < (r * t) / (1 + r) := by
  rw [div_lt_iff₀ (show 0 < t-p by linarith), lt_div_iff₀ (show 0 < 1+r by linarith)]
  constructor <;> intro h <;> nlinarith
