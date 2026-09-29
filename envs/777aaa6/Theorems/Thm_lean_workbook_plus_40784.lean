-- Prove2me | Theorems.Thm_lean_workbook_plus_40784
-- name    : lean_workbook_plus_40784
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/37c44759-53bf-401e-9037-dc8d8af7e698
-- statement:
--   Prove that $(3+2xy)(18-6xy+x^2y^2)\leq 64$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40784 : ∀ x y : ℝ, (3+2*x*y)*(18-6*x*y+(x*y)^2) ≤ 64   :=  by sorry
