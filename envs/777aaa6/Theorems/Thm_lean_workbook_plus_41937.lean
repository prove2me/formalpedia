-- Prove2me | Theorems.Thm_lean_workbook_plus_41937
-- name    : lean_workbook_plus_41937
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/355949c3-8674-4904-9ebc-a47602a258ca
-- statement:
--   $(xy+yz+zx)^2\geq 3(x+y+z)xyz$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_41937 (x y z : ℝ) : (x*y + y*z + z*x)^2 ≥ 3*(x + y + z)*x*y*z   :=  by sorry
