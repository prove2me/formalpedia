-- Prove2me | Theorems.Thm_lean_workbook_plus_26982
-- name    : lean_workbook_plus_26982
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/09e63b11-937b-42da-b348-670b7f4b2fb1
-- statement:
--   Prove that if $a,b,c$ are positive real numbers, then $\frac{9}{2(a+b+c)}\le \frac{1}{b+c}+\frac{1}{c+a}+\frac{1}{a+b}\le \frac{1}{2}(\frac{1}{a}+\frac{1}{b}+\frac{1}{c}).$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26982 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (9 / (2 * (a + b + c))) ≤ (1 / (b + c) + 1 / (c + a) + 1 / (a + b)) ∧ (1 / (b + c) + 1 / (c + a) + 1 / (a + b)) ≤ (1 / 2) * (1 / a + 1 / b + 1 / c)   :=  by sorry
