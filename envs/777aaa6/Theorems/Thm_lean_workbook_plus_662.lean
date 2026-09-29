-- Prove2me | Theorems.Thm_lean_workbook_plus_662
-- name    : lean_workbook_plus_662
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/8d18dfc4-726e-4e82-9008-b77ca36831df
-- statement:
--   If $ a,b$ both odd then $ X=a^2+b^2+26$ even and $ Y=5ab$ odd.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_662 : ∀ a b : ℤ, Odd a ∧ Odd b → Even (a^2 + b^2 + 26) ∧ Odd (5 * a * b)   :=  by sorry
