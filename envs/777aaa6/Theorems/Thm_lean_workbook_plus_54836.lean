-- Prove2me | Theorems.Thm_lean_workbook_plus_54836
-- name    : lean_workbook_plus_54836
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/59ff4534-e712-4d4f-8efa-db34e2d607c7
-- statement:
--   Prove that\n\n$ \sum \frac {(a - b)^2(b - c)^2(c - a)^2}{(a + b)(a + c)(a^2 + bc) }\ge 0.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54836 :
  ∀ a b c : ℝ, (a - b) ^ 2 * (b - c) ^ 2 * (c - a) ^ 2 / (a + b) / (a + c) / (a ^ 2 + b * c) + (b - a) ^ 2 * (c - b) ^ 2 * (a - c) ^ 2 / (b + a) / (b + c) / (b ^ 2 + a * c) + (c - a) ^ 2 * (a - b) ^ 2 * (b - c) ^ 2 / (c + a) / (c + b) / (c ^ 2 + a * b) ≥ 0   :=  by sorry
