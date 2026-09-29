-- Prove2me | Theorems.Thm_lean_workbook_plus_3735
-- name    : lean_workbook_plus_3735
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/fcad7925-a7d8-41a2-9391-21f57c908f54
-- statement:
--   Let $a, b \ge 1.$ Prove that $ab(a + 2b - 10) + 8(3a + b)\geq 25$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3735 (a b : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) : a * b * (a + 2 * b - 10) + 8 * (3 * a + b) ≥ 25   :=  by sorry
