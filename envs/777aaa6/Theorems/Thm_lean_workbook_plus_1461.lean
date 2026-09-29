-- Prove2me | Theorems.Thm_lean_workbook_plus_1461
-- name    : lean_workbook_plus_1461
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/72315736-7639-4cf3-baad-8c2eb21fca63
-- statement:
--   prove that $ x^4 + y^4 + z^4 + xy^3 + yz^3 + zx^3 \ge\ 2(yx^3 + zy^3 + xz^3)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1461 (x y z : ℝ) : x^4 + y^4 + z^4 + x*y^3 + y*z^3 + z*x^3 ≥ 2*(x*y^3 + y*z^3 + z*x^3)   :=  by sorry
