-- Prove2me | Theorems.Thm_lean_workbook_plus_39971
-- name    : lean_workbook_plus_39971
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/a27c13de-88bf-4352-a586-926cac395a42
-- statement:
--   Find all functions $f: {\mathbb Z}\to {\mathbb Z}$ which satisfy $f\left(x+y+f(y)\right) = f(x) + 2y\; \; \; ,\; \; \forall x,y \in {\mathbb Z}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39971 : ∃ f : ℤ → ℤ, f (x + y + f y) = f x + 2 * y   :=  by sorry
