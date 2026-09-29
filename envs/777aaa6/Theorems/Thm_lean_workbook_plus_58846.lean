-- Prove2me | Theorems.Thm_lean_workbook_plus_58846
-- name    : lean_workbook_plus_58846
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/c235f6f9-9062-492e-816b-5ffe03a3186f
-- statement:
--   Prove that $ \ln(1+x)\leq x$ for $ x>0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58846 (x : ℝ) (hx : 0 < x) : Real.log (1 + x) ≤ x   :=  by sorry
