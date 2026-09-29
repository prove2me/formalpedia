-- Prove2me | Theorems.Thm_WorkbookSource_problem_31792
-- name    : WorkbookSource.problem_31792
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:58:51.098747+00:00
-- url     : https://prove2.me/theorems/e2e4affd-e145-412e-be7e-59827c4fa086
-- title:
--   A fifth-power consequence of a cubic bound
-- statement:
--   If $ \{x,y,z\}\subset[ - 2, + \infty)$ and $ x^3 + y^3 + z^3 \geq x^2 + y^2 + z^2$ then $ x^5 + y^5 + z^5 \geq x^2 + y^2 + z^2$ is still true.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_31792` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_31792; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_31792 (x y z : ℝ) (hx : -2 ≤ x) (hy : -2 ≤ y) (hz : -2 ≤ z) (h : x^3 + y^3 + z^3 ≥ x^2 + y^2 + z^2) : x^5 + y^5 + z^5 ≥ x^2 + y^2 + z^2  :=  by sorry
