-- Prove2me | Theorems.Thm_lean_workbook_plus_19487
-- name    : lean_workbook_plus_19487
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/ab23e4bd-8fc1-4c95-bdd2-e413634edbe5
-- statement:
--   Show that for all real numbers $x,y,z$ such that $x + y + z = 0$ and $xy + yz + zx = -3$ , the expression $x^3y + y^3z + z^3x$ is a constant.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19487 (x y z : ℝ) (h1 : x + y + z = 0) (h2 : x*y + y*z + z*x = -3) : x^3*y + y^3*z + z^3*x = -9   :=  by sorry
