-- Prove2me | Theorems.Thm_lean_workbook_plus_137
-- name    : lean_workbook_plus_137
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/ea17ea4c-cef0-437e-be63-12d2b89f8786
-- statement:
--   Prove that $\ln(e^{\pi})$ is equal to $\pi$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_137 : Real.log (Real.exp π) = π   :=  by sorry
