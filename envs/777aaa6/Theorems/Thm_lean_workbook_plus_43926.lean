-- Prove2me | Theorems.Thm_lean_workbook_plus_43926
-- name    : lean_workbook_plus_43926
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/1c33f971-d0ba-4320-91ef-d04c30ea625b
-- statement:
--   for $a;b;c\geq 1$ ; $a+b+c=1$ . Prove $a^{2}+b^{2}+c^{2}+\sqrt{12abc}\leq 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_43926 (a b c : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hab : a + b + c = 1) : a^2 + b^2 + c^2 + Real.sqrt (12 * a * b * c) ≤ 1   :=  by sorry
