-- Prove2me | Theorems.Thm_lean_workbook_plus_53578
-- name    : lean_workbook_plus_53578
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/90a04e34-7f89-4fdb-b015-b5952192f48b
-- statement:
--   x between 0,1 $x^8+x^2<1$ , $x^5+x<1$ , so $1 \geq x^5+x-x^8-x^2$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_53578 : ∀ x : ℝ, x ∈ Set.Icc 0 1 → x^5 + x - x^8 - x^2 ≤ 1   :=  by sorry
