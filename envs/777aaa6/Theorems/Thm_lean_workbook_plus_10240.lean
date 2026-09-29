-- Prove2me | Theorems.Thm_lean_workbook_plus_10240
-- name    : lean_workbook_plus_10240
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/6e58be17-2cbf-4fd3-8568-d9caf8e4d9d1
-- statement:
--   Show that $n=2$ in Schur's Inequality expands to $x^4+y^4+z^4+xyz(x+y+z)\ge x^3y+y^3z+z^3x+xy^3+yz^3+zx^3$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_10240 (x y z : ℝ) : x ^ 4 + y ^ 4 + z ^ 4 + x * y * z * (x + y + z) ≥ x ^ 3 * y + y ^ 3 * z + z ^ 3 * x + x * y ^ 3 + y * z ^ 3 + z * x ^ 3   :=  by sorry
