-- Prove2me | Theorems.Thm_lean_workbook_plus_59344
-- name    : lean_workbook_plus_59344
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/0b4ab274-6e62-4b1e-b89d-ad180e4f7d8f
-- statement:
--   Compute $(1-\frac{1}{2^2})(1-\frac{1}{3^2})\dots (1-\frac{1}{9^2})(1-\frac{1}{10^2})$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59344 : (∏ i in Finset.Icc 2 10, (1 - 1 / (i + 1) ^ 2)) = 11 / 20   :=  by sorry
