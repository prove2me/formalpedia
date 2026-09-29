-- Prove2me | Theorems.Thm_lean_workbook_plus_29547
-- name    : lean_workbook_plus_29547
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/220275b1-b952-4fc2-8b3c-91a15d7d4fbb
-- statement:
--   Let $a,b\geq 0$ and $a^3+b^3=a-b.$ Prove that $(a-b)^4\leq (1-4ab)(1-ab)^2.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29547 {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a^3 + b^3 = a - b) : (a - b)^4 ≤ (1 - 4 * a * b) * (1 - a * b)^2   :=  by sorry
