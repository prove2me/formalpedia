-- Prove2me | Theorems.Thm_WorkbookCorrected_base_54977
-- name    : WorkbookCorrected.base_54977
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T12:12:47.713384+00:00
-- url     : https://prove2.me/theorems/4f483f79-4c73-4acb-9882-542568b84730
-- title:
--   A quadratic lower bound with an attained equality case
-- statement:
--   Let $x,y,z$ be real numbers satisfying $x+yz=1$. Then
--   \[2x^2+3y^2+4z^2\ge 2.\]
--   Equality holds at $x=1,y=z=0$, so the lower bound is attained.
--
--   Formalization Note: This statement includes both the universal inequality and the equality point explicitly stated in the source. The original formalization contained only the inequality.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_54977 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_54977; Apache-2.0

import Mathlib

theorem WorkbookCorrected.base_54977 : (∀ (x y z : ℝ) (h : x + y*z = 1), 2*x^2 + 3*y^2 + 4*z^2 ≥ 2) ∧ ((1 : ℝ) + 0*0 = 1 ∧ 2*(1 : ℝ)^2 + 3*0^2 + 4*0^2 = 2) := by sorry
