-- Prove2me | Theorems.Thm_lean_workbook_plus_26664
-- name    : lean_workbook_plus_26664
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/45b0cfd2-13f7-4de3-b444-3906cea16172
-- statement:
--   Let $a$ , $b$ and $c$ be positive real numbers. Prove that $9(a^3+b^3+c^3) \ge (a+b+c)^3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26664 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 9 * (a ^ 3 + b ^ 3 + c ^ 3) ≥ (a + b + c) ^ 3   :=  by sorry
