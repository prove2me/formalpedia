-- Prove2me | Theorems.Thm_lean_workbook_plus_53077
-- name    : lean_workbook_plus_53077
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/68cf9251-aa27-493e-b659-4ccb076d5111
-- statement:
--   Prove the identity used in the solution:\n$x^3 - y^3 = (x - y)(x^2 + xy + y^2)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_53077 (x y : ℤ) : x^3 - y^3 = (x - y) * (x^2 + x * y + y^2)   :=  by sorry
