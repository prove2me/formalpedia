-- Prove2me | Theorems.Thm_lean_workbook_plus_19842
-- name    : lean_workbook_plus_19842
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/b8764492-a7e3-4fcc-9b86-3069b5c2b457
-- statement:
--   $ \leftrightarrow$ $ 2\left(ab+bc+ca\right)\left(ab+bc+ca\right)\geq 6abc\left(a+b+c\right)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19842 {a b c : ℝ} : 2 * (a * b + b * c + c * a) * (a * b + b * c + c * a) ≥ 6 * a * b * c * (a + b + c)   :=  by sorry
