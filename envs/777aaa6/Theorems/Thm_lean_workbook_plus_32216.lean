-- Prove2me | Theorems.Thm_lean_workbook_plus_32216
-- name    : lean_workbook_plus_32216
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/07bc0f71-f2ec-4ba2-8e89-cb6bcac9ba77
-- statement:
--   Prove that \n\n $\cos (a+b+c) + \cos (a+b-c) + \cos (a+c-b) + \cos ( b+c-a) = 4 \cos a \cos b \cos c$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32216 {a b c : ℝ} : (Real.cos (a + b + c) + Real.cos (a + b - c) + Real.cos (a + c - b) + Real.cos (b + c - a)) = 4 * Real.cos a * Real.cos b * Real.cos c   :=  by sorry
