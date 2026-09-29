-- Prove2me | Theorems.Thm_lean_workbook_plus_54172
-- name    : lean_workbook_plus_54172
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/3bd9a18a-720d-4f2b-bc74-1997eb4dae95
-- statement:
--   We need to prove that $(x^2+y^2+z^2)^3\geq(x+y+z)^2(x^2+y^2+z^2-xy-xz-yz)^2$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54172 (x y z : ℝ) :
  (x^2 + y^2 + z^2)^3 ≥ (x + y + z)^2 * (x^2 + y^2 + z^2 - x * y - x * z - y * z)^2   :=  by sorry
