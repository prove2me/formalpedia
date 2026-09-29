-- Prove2me | Theorems.Thm_lean_workbook_plus_75741
-- name    : lean_workbook_plus_75741
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/b30b236a-3890-44b6-a28a-db87b631ed2d
-- statement:
--   From AM-GM \n $\left(\frac{1}{a}+\frac{1}{b}+\frac{1}{c}\right)^3\geq \frac{27}{a b c}$\n
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75741 : ∀ a b c : ℝ, (1 / a + 1 / b + 1 / c) ^ 3 ≥ 27 / (a * b * c)   :=  by sorry
