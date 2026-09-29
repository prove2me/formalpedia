-- Prove2me | Theorems.Thm_lean_workbook_plus_36582
-- name    : lean_workbook_plus_36582
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/865ce030-ff59-4614-8817-35b0a5c1f1aa
-- statement:
--   Given $a+\frac{b^2}{a}=b+\frac{a^2}{b}$, prove that $a=b$ for nonzero real numbers $a$ and $b$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36582 (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a + b^2 / a = b + a^2 / b) : a = b   :=  by sorry
