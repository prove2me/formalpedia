-- Prove2me | Theorems.Thm_lean_workbook_plus_40944
-- name    : lean_workbook_plus_40944
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/faf2ec93-96c5-46c6-b710-7454ed63b1bb
-- statement:
--   Show regoriously that the function $\sin(x^2+y^2)$ is continuous at $(0,0)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40944 (x y : ℝ) : Continuous (fun p : ℝ × ℝ => sin (p.1^2 + p.2^2))   :=  by sorry
