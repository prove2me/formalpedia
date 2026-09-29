-- Prove2me | Theorems.Thm_lean_workbook_plus_38963
-- name    : lean_workbook_plus_38963
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/8c91fbc8-a3c9-4ff4-843b-66c2de7802dd
-- statement:
--   Let $ u = \sqrt{x + a}, v = \sqrt{x - a}$ . Then $ u^2 - v^2 = 2a$ and
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38963  (x a : ℝ)
  (u v : ℝ)
  (h₀ : u = Real.sqrt (x + a))
  (h₁ : v = Real.sqrt (x - a))
  (h₂ : 0 ≤ x + a)
  (h₃ : 0 ≤ x - a) :
  u^2 - v^2 = 2 * a   :=  by sorry
