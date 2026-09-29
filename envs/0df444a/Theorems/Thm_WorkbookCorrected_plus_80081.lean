-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_80081
-- name    : WorkbookCorrected.plus_80081
-- status  : Proved
-- author  : @Rizwan G Mir
-- created : 2026-09-24T21:31:15.254364+00:00
-- url     : https://prove2.me/theorems/77f7af30-99f5-4ff0-950c-74f4b7b1bae9
-- title:
--   Absolute value of log(k)/k^2 is nonnegative
-- statement:
--   For every natural number $k$, $\left|\dfrac{\log k}{k^2}\right| \ge 0$.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_80081`, whose `Real.log` reference is unresolvable under its narrow `Mathlib.Analysis.Complex.Basic` preamble.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_80081 (Apache-2.0).

import Mathlib

theorem WorkbookCorrected.plus_80081 : ∀ k : ℕ, (0 : ℝ) ≤ |(Real.log k)/k^2| := by sorry
