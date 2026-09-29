-- Prove2me | Theorems.Thm_lean_workbook_plus_52421
-- name    : lean_workbook_plus_52421
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/7e3f91c5-9716-40e5-825d-ead8b162e6e6
-- statement:
--   Denote $a=3x, b=4y, c=5z; x,y,z>0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52421 (a b c x y z : ℝ) (h : a = 3 * x ∧ b = 4 * y ∧ c = 5 * z) (hx : x > 0 ∧ y > 0 ∧ z > 0) : a > 0 ∧ b > 0 ∧ c > 0   :=  by sorry
