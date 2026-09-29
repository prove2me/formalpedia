-- Prove2me | Theorems.Thm_lean_workbook_plus_40945
-- name    : lean_workbook_plus_40945
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/7cdb7725-5234-4f76-b995-b02998038c30
-- statement:
--   Prove that if $ \left | a-b \right |<\frac{\left | b \right |}2 $ , then $ \left | a \right |>\frac{\left | b \right |}{2} $ . \na,b are real numbers
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40945 (a b : ℝ) (h : abs (a - b) < abs b / 2) : abs a > abs b / 2   :=  by sorry
