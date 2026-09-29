-- Prove2me | Theorems.Thm_lean_workbook_plus_370
-- name    : lean_workbook_plus_370
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/b06259e8-b16f-4abc-b56c-11335e558c0a
-- statement:
--   Simple its just $x^3 + y^3 + z^3 - 3xyz = (x + y + z)(x^2 + y^2 + z^2 - xy - yz - xz)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_370 {x y z : ℝ} : x ^ 3 + y ^ 3 + z ^ 3 - 3 * x * y * z = (x + y + z) * (x ^ 2 + y ^ 2 + z ^ 2 - x * y - y * z - x * z)   :=  by sorry
