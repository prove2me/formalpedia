-- Prove2me | Theorems.Thm_lean_workbook_plus_79395
-- name    : lean_workbook_plus_79395
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/a50f11f4-6976-4f44-bf31-ee6d1a6a324f
-- statement:
--   $abc(ab+ac+bc)\leq a^3b^2+b^3c^2+c^3a^2\Leftrightarrow\sum_{cyc}7a^3b^2\geq7\cdot\sum_{cyc}a^2b^2c.$ But $\sum_{cyc}7a^3b^2=\sum_{cyc}(4a^3b^2+2b^3c^2+c^3a^2)\geq7\cdot\sum_{cyc}\sqrt[7]{a^{12+2}b^{8+6}c^{4+3}}=7\cdot\sum_{cyc}a^2b^2c.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79395  (a b c : ℝ) :
  a * b * c * (a * b + b * c + c * a) ≤ a^3 * b^2 + b^3 * c^2 + c^3 * a^2 ↔ 7 * a^3 * b^2 + 7 * b^3 * c^2 + 7 * c^3 * a^2 ≥ 7 * (a^2 * b^2 * c + b^2 * c^2 * a + c^2 * a^2 * b)   :=  by sorry
