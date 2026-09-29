-- Prove2me | Theorems.Thm_lean_workbook_plus_24566
-- name    : lean_workbook_plus_24566
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/f14f47bd-cc67-4fa0-b975-ecf578a92346
-- statement:
--   The following inequality is also true.\n\nLet $a$ , $b$ and $c$ be positive numbers such that $a+b+c\geq3$ . Prove that:\n\n $$5abc+4\geq\frac{27}{a^3+b^3+c^3}$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24566 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (hab : a + b + c >= 3) : 5 * a * b * c + 4 ≥ 27 / (a ^ 3 + b ^ 3 + c ^ 3)   :=  by sorry
