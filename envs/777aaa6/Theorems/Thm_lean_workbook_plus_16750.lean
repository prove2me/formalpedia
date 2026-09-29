-- Prove2me | Theorems.Thm_lean_workbook_plus_16750
-- name    : lean_workbook_plus_16750
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/9a9b1b2a-5cfd-4373-baed-971f5877669f
-- statement:
--   Prove the identity $\exp(a+b) = \exp(a) \exp(b)$ using the power series definition of the exponential function.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16750 (a b : ℝ) : exp (a + b) = exp a * exp b   :=  by sorry
