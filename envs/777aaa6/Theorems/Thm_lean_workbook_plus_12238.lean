-- Prove2me | Theorems.Thm_lean_workbook_plus_12238
-- name    : lean_workbook_plus_12238
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/783bcf4e-2bcf-421b-9e6a-c78ccc1c7148
-- statement:
--   Let n be a positive integer, prove that \n\n $ \dfrac{1}{n+1}+\dfrac{1}{n+2}+...+\dfrac{1}{2n}\ge\dfrac{1}{2}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12238 : ∀ n : ℕ, (∑ k in Finset.Icc (n + 1) (2 * n), (1 / k)) ≥ 1 / 2   :=  by sorry
