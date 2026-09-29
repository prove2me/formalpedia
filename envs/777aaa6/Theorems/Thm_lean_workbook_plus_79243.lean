-- Prove2me | Theorems.Thm_lean_workbook_plus_79243
-- name    : lean_workbook_plus_79243
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/5634e58f-dbbc-44fd-bd0e-bc8c3243288e
-- statement:
--   Prove that $(log_{yz}x^4yz)(log_{zx}xy^4z)(log_{xy}xyz^4)>27$, given $x,y,z>1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79243 : ∀ x y z : ℝ, x > 1 ∧ y > 1 ∧ z > 1 → (Real.logb (y * z) (x ^ 4 * y * z) * Real.logb (z * x) (x * y ^ 4 * z) * Real.logb (x * y) (x * y * z ^ 4)) > 27   :=  by sorry
