-- Prove2me | Theorems.Thm_lean_workbook_plus_71556
-- name    : lean_workbook_plus_71556
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/ae35a936-4c0f-470a-a3d0-b7ffb010e6c9
-- statement:
--   Prove that \n $\forall x,y,z \in \mathbb{R} ; (x+y+z=0) \Longrightarrow (x^3+y^3+z^3=3xyz)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71556 (x y z : ℝ) (h : x + y + z = 0) :
  x^3 + y^3 + z^3 = 3 * x * y * z   :=  by sorry
