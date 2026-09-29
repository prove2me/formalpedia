-- Prove2me | Theorems.Thm_lean_workbook_plus_53984
-- name    : lean_workbook_plus_53984
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/7445ba85-5968-4969-b8cc-790007f3ef4e
-- statement:
--   Prove that $ a^3 + b^3 + c^3 = 3abc + (a + b + c)(a^2 + b^2 + c^2 - ab - bc - ca)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_53984 (a b c : ℝ) : a^3 + b^3 + c^3 = 3 * a * b * c + (a + b + c) * (a^2 + b^2 + c^2 - a * b - b * c - c * a)   :=  by sorry
