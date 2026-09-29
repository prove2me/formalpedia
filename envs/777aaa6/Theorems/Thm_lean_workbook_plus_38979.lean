-- Prove2me | Theorems.Thm_lean_workbook_plus_38979
-- name    : lean_workbook_plus_38979
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/28db77d0-fe43-43fa-b87a-cee6a9acd6ae
-- statement:
--   $ \Longleftrightarrow 9(x^2 + y^2 + z^2)(x^4 + 2y^2x^2 + 2x^2z^2 + y^4 + 2y^2z^2$ $ + z^4 - 3yz^2x - 3yzx^2 - 3y^2zx)\geq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38979 (x y z : ℝ) : 9 * (x ^ 2 + y ^ 2 + z ^ 2) * (x ^ 4 + 2 * y ^ 2 * x ^ 2 + 2 * x ^ 2 * z ^ 2 + y ^ 4 + 2 * y ^ 2 * z ^ 2 + z ^ 4 - 3 * y * z ^ 2 * x - 3 * y * z * x ^ 2 - 3 * y ^ 2 * z * x) ≥ 0   :=  by sorry
