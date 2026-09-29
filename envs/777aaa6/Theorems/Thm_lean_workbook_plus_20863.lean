-- Prove2me | Theorems.Thm_lean_workbook_plus_20863
-- name    : lean_workbook_plus_20863
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/cfdc2ac5-24f9-4022-8cf3-12b6940fa352
-- statement:
--   Prove $ (\log_{a}b) \times (\log_{c}d) = (\log_{c}b) \times (\log_{a}d)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20863 (a b c d : ℝ) : (Real.log b / Real.log a) * (Real.log d / Real.log c) = (Real.log b / Real.log c) * (Real.log d / Real.log a)   :=  by sorry
