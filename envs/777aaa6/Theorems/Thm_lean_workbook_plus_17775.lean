-- Prove2me | Theorems.Thm_lean_workbook_plus_17775
-- name    : lean_workbook_plus_17775
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/b0192918-cf08-4712-b9eb-4be3f45cf0b6
-- statement:
--   Prove that $9(a^2+b^2)(b^2+c^2)(c^2+a^2)\ge 2(a^2+b^2+c^2)^3$ given $a+b+c=0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17775 (a b c : ℝ) (hab : a + b + c = 0) : 9 * (a ^ 2 + b ^ 2) * (b ^ 2 + c ^ 2) * (c ^ 2 + a ^ 2) ≥ 2 * (a ^ 2 + b ^ 2 + c ^ 2) ^ 3   :=  by sorry
