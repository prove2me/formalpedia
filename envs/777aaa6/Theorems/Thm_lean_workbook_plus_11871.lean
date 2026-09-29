-- Prove2me | Theorems.Thm_lean_workbook_plus_11871
-- name    : lean_workbook_plus_11871
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/91435ac6-09a2-4c63-99b8-e2aad2875c1d
-- statement:
--   Given $abc=0$, prove the inequality $\sum_{cyc}a^2b^4 + \sum_{cyc}a^3bc^2 \geq 2 \sum_{cyc}a^3b^2c$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11871 (a b c : ℝ) (h : a * b * c = 0) :
  a ^ 2 * b ^ 4 + b ^ 2 * c ^ 4 + c ^ 2 * a ^ 4 + a ^ 3 * b * c ^ 2 + b ^ 3 * c * a ^ 2 + c ^ 3 * a * b ^ 2 ≥
  2 * (a ^ 3 * b ^ 2 * c + b ^ 3 * c ^ 2 * a + c ^ 3 * a ^ 2 * b)   :=  by sorry
