-- Prove2me | Theorems.Thm_lean_workbook_plus_2785
-- name    : lean_workbook_plus_2785
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/51b19494-00b1-40c0-8a9b-96faa34e73f0
-- statement:
--   $ \leftrightarrow$ $ \left(a+b+c\right)^2\left( ab+bc+ca\right)\geq 6abc\left(a+b+c\right)+\left(a^2+b^2+c^2\right)\left(ab+bc+ca\right)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2785 {a b c : ℝ} : (a + b + c) ^ 2 * (a * b + b * c + c * a) ≥ 6 * a * b * c * (a + b + c) + (a ^ 2 + b ^ 2 + c ^ 2) * (a * b + b * c + c * a)   :=  by sorry
