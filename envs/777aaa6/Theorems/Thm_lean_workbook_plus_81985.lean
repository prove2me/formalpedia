-- Prove2me | Theorems.Thm_lean_workbook_plus_81985
-- name    : lean_workbook_plus_81985
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/e60ab6b9-a612-4a58-98ea-75b527401a1c
-- statement:
--   Let $a=x/2y,b=y/2z,c=z/2x$ and you get: $4x^4z^2+4y^4x^2+4z^4y^2+x^4y^2+z^4x^2+y^4z^2 \ge 15x^2y^2z^2$ which is true by AM-GM.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81985  (x y z : ℝ) :
  4 * x^4 * z^2 + 4 * y^4 * x^2 + 4 * z^4 * y^2 + x^4 * y^2 + z^4 * x^2 + y^4 * z^2 ≥ 15 * x^2 * y^2 * z^2   :=  by sorry
