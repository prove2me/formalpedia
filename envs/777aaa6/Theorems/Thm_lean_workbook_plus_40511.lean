-- Prove2me | Theorems.Thm_lean_workbook_plus_40511
-- name    : lean_workbook_plus_40511
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/8cd77297-aedf-4d16-9d31-bc209b82897f
-- statement:
--   For positive real numbers $a,b$ and positive integers $n$ , prove that $\frac{1}{na+b}+\frac{1}{a+nb} \leq \frac{1}{n+1}(\frac{1}{a} + \frac{1}{b}).$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40511 (a b : ℝ) (n : ℕ) (ha : 0 < a) (hb : 0 < b) : (1 / (n * a + b) + 1 / (a + n * b)) ≤ (1 / (n + 1) * (1 / a + 1 / b))   :=  by sorry
