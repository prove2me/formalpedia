-- Prove2me | Theorems.Thm_lean_workbook_plus_28263
-- name    : lean_workbook_plus_28263
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/331f0eda-4960-43c6-a271-bd4d72f66945
-- statement:
--   Find the value of $(1-\frac{1}{2^2})(1-\frac{1}{3^2})(1-\frac{1}{4^2}) \cdots (1-\frac{1}{99^2})$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_28263 (n : ℕ) : (∏ k in Finset.Icc 1 99, (1 - 1 / (k + 1) ^ 2)) = 50 / 99   :=  by sorry
