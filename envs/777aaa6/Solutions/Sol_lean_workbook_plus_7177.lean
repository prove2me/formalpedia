-- Prove2me | solution 1 for lean_workbook_plus_7177
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:12:51.092002+00:00
-- url     : https://prove2.me/submissions/db90b859-ae0a-4f35-8cf8-05e580234cf4

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution {a b c : ℝ} (h : a^2 + b^2 = c^2) : ∃ k : ℝ, k^2 * a^2 + k^2 * b^2 = k^2 * c^2 := by
  have hscale : ∀ k : ℝ, k^2*a^2+k^2*b^2=k^2*c^2 := by
    intro k
    linear_combination k^2 * h
  exact ⟨1, hscale 1⟩
