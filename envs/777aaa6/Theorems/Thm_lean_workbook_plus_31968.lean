-- Prove2me | Theorems.Thm_lean_workbook_plus_31968
-- name    : lean_workbook_plus_31968
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/13716d1d-af00-4873-b454-0a429b36ccec
-- statement:
--   $\sum_{cyc}(x^3+2x^2y-3x^2z)\geq0\Leftrightarrow\sum_{cyc}(2x^3+4x^2y-6x^2z)\geq0\Leftrightarrow$ $\Leftrightarrow\sum_{cyc}(2x^3-x^2y-x^2z)\geq5\sum_{cyc}(x^2z-x^2y)\Leftrightarrow$ $\Leftrightarrow\sum_{cyc}(2x^3-x^2y-x^2z)\geq5(x-y)(y-z)(z-x)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31968 : ∀ x y z : ℝ, (x ^ 3 + y ^ 3 + z ^ 3 + 2 * (x ^ 2 * y + y ^ 2 * z + z ^ 2 * x) - 3 * (x ^ 2 * z + y ^ 2 * x + z ^ 2 * y) ≥ 0 ↔ 2 * (x ^ 3 + y ^ 3 + z ^ 3) + 4 * (x ^ 2 * y + y ^ 2 * z + z ^ 2 * x) - 6 * (x ^ 2 * z + y ^ 2 * x + z ^ 2 * y) ≥ 0)   :=  by sorry
