-- Prove2me | Theorems.Thm_lean_workbook_plus_47064
-- name    : lean_workbook_plus_47064
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/f8dd81af-b152-464a-ad69-11e2aa94d753
-- statement:
--   $\frac{1}{2}(\frac{1}{a}+\frac{1}{b}+\frac{1}{c})\geq\frac{1}{a+b}+\frac{1}{b+c}+\frac{1}{c+a}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47064 {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (1 / 2) * (1 / a + 1 / b + 1 / c) ≥ 1 / (a + b) + 1 / (b + c) + 1 / (c + a)   :=  by sorry
