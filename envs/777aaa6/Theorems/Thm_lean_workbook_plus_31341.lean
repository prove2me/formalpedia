-- Prove2me | Theorems.Thm_lean_workbook_plus_31341
-- name    : lean_workbook_plus_31341
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/0cb5a6f6-faf6-48ff-9cab-ad5a2bd947f1
-- statement:
--   Prove or disprove the associativity of the operation $*$: $(x*y)*z=x*(y*z)$ for all $x,y,z\in\mathbb{Z}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31341 : ∀ x y z : ℤ, x * y * z = x * (y * z)   :=  by sorry
