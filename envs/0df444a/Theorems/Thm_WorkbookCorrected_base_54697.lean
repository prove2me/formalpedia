-- Prove2me | Theorems.Thm_WorkbookCorrected_base_54697
-- name    : WorkbookCorrected.base_54697
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T12:12:51.128597+00:00
-- url     : https://prove2.me/theorems/e257e6cb-824e-4d7a-b058-5a8cfe21f2a7
-- title:
--   Strict positivity of a quartic on the nonnegative real axis
-- statement:
--   Let $x$ be a nonnegative real number. Then
--   \[663x^4-620x^3-790x^2+284x+503>0.\]
--   This establishes strict positivity of the quartic throughout the nonnegative real axis.
--
--   Formalization Note: The source record omitted the type of x, causing Lean to default to natural-number arithmetic. This corrected statement explicitly uses real numbers and preserves the source inequality and nonnegative domain.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_54697 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_54697; Apache-2.0

import Mathlib

theorem WorkbookCorrected.base_54697 (x : ℝ) (hx : 0 ≤ x) : 663*x^4 - 620*x^3 - 790*x^2 + 284*x + 503 > 0 := by sorry
