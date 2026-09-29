-- Prove2me | Theorems.Thm_lean_workbook_plus_71895
-- name    : lean_workbook_plus_71895
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/193bdaa6-2ef2-423c-9b11-f49633198c8f
-- statement:
--   Let $a,b,c>0$ . Prove that $\dfrac{a+b+c}{1+a+b+c}\geq\dfrac{a}{1+3a}+\dfrac{b}{1+3b}+\dfrac{c}{1+3c}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71895 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b + c) / (1 + a + b + c) ≥ a / (1 + 3 * a) + b / (1 + 3 * b) + c / (1 + 3 * c)   :=  by sorry
