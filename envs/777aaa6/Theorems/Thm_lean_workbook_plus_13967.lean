-- Prove2me | Theorems.Thm_lean_workbook_plus_13967
-- name    : lean_workbook_plus_13967
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/25244fbf-c26e-4ede-9068-e4b091e1f48a
-- statement:
--   This is just $\frac{3! \cdot 3!}{6!}=\boxed{\frac{1}{20}}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13967 :
  ((3! * 3!):ℝ) / 6! = 1 / 20   :=  by sorry
