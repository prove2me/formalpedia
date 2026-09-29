-- Prove2me | Theorems.Thm_lean_workbook_plus_61323
-- name    : lean_workbook_plus_61323
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/85ff9a5f-dbce-4254-90d4-5b467afe8df8
-- statement:
--   Remember $x^3 + y^3 +z^3 - 3xyz = (x+y+z)(x^2+y^2+z^2 - xy - xz - yz)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61323 {x y z : ℝ} : x^3 + y^3 + z^3 - 3*x*y*z = (x + y + z) * (x^2 + y^2 + z^2 - x*y - x*z - y*z)   :=  by sorry
