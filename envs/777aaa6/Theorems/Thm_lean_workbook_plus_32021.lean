-- Prove2me | Theorems.Thm_lean_workbook_plus_32021
-- name    : lean_workbook_plus_32021
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/fce6ad34-8b21-4336-ba3f-8152f5bd2f60
-- statement:
--   Prove that $x^2+y^2+z^2+x^2y^2z^2\geq 4xyz$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32021 (x y z : ℝ) : x^2 + y^2 + z^2 + x^2*y^2*z^2 ≥ 4*x*y*z   :=  by sorry
