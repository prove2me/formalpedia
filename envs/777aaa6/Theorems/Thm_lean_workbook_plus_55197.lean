-- Prove2me | Theorems.Thm_lean_workbook_plus_55197
-- name    : lean_workbook_plus_55197
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/cfe35655-f550-4517-a60d-8d495911758a
-- statement:
--   Prove that $\frac{ab}{a+b} * \frac{bc}{b+c} \le \frac{(a+b)(b+c)}{(a+b)+(b+c)}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55197 : ∀ a b c : ℝ, (a * b) / (a + b) * (b * c) / (b + c) ≤ (a + b) * (b + c) / (a + b + (b + c))   :=  by sorry
