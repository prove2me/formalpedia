-- Prove2me | Theorems.Thm_WorkbookCorrected_cos_sq_double_angle_79936
-- name    : WorkbookCorrected.cos_sq_double_angle_79936
-- status  : Proved
-- author  : @Rizwan G Mir
-- created : 2026-09-24T19:43:46.405323+00:00
-- url     : https://prove2.me/theorems/fbccb628-fd85-4ec0-914b-280154c3572b
-- title:
--   Power reduction: cos^2(x) = (1+cos(2x))/2
-- statement:
--   For every real $x$, $\cos^2(x) = \dfrac{1+\cos(2x)}{2}$ (the cosine power-reduction / half-angle identity).
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_79936`, whose bare `cos` is not resolvable under its narrow `Mathlib.Analysis.Complex.Basic` preamble.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_79936 (Apache-2.0).

import Mathlib

theorem WorkbookCorrected.cos_sq_double_angle_79936 : ∀ x : ℝ, Real.cos x ^ 2 = (1 + Real.cos (2 * x)) / 2 := by sorry
