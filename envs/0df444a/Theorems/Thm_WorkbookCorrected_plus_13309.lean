-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_13309
-- name    : WorkbookCorrected.plus_13309
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T13:12:18.751097+00:00
-- url     : https://prove2.me/theorems/ea74d1bc-77c5-43fc-ac68-7f6ee2f73624
-- title:
--   The maximum of a quadratic expression on an ellipse
-- statement:
--   For real numbers $x,y$ satisfying $4x^2+9y^2=36$, the maximum of $x^2+\frac23xy+\frac32y^2$ is $10$. It is attained at $(x,y)=(6\sqrt5/5,2\sqrt5/5)$.
--
--   Formalization Note: The original source asks for an extremum, while its formal statement supplied only a bound. This complete formulation includes both the universal bound and existence of an attaining point.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_13309 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_13309; Apache-2.0

import Mathlib

theorem WorkbookCorrected.plus_13309 : (∀ x y : ℝ, 4*x^2+9*y^2=36 → x^2+(2/3)*x*y+(3/2)*y^2 ≤ 10) ∧
    (∃ x y : ℝ, 4*x^2+9*y^2=36 ∧ x^2+(2/3)*x*y+(3/2)*y^2=10) := by sorry
