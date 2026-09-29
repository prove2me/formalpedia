-- Prove2me | Theorems.Thm_lean_workbook_plus_47215
-- name    : lean_workbook_plus_47215
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/757cc90b-ba7d-4d82-9dfa-358ff6690a6f
-- statement:
--   Prove that if $ a,b,c$ are positive real numbers, then:\n\n$ \frac{9}{a+b+c} \le 2 \left( \frac{1}{a+b}+\frac{1}{b+c}+\frac{1}{c+a} \right) \le \frac{1}{a}+\frac{1}{b}+\frac{1}{c}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47215 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (9 / (a + b + c) : ℝ) ≤ 2 * (1 / (a + b) + 1 / (b + c) + 1 / (c + a)) ∧ (2 * (1 / (a + b) + 1 / (b + c) + 1 / (c + a)) : ℝ) ≤ (1 / a + 1 / b + 1 / c)   :=  by sorry
