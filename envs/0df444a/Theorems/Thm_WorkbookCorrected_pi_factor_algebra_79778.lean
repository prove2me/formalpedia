-- Prove2me | Theorems.Thm_WorkbookCorrected_pi_factor_algebra_79778
-- name    : WorkbookCorrected.pi_factor_algebra_79778
-- status  : Proved
-- author  : @Rizwan G Mir
-- created : 2026-09-24T19:43:52.894647+00:00
-- url     : https://prove2.me/theorems/516d1531-8925-46f5-9968-d7516e8424f8
-- title:
--   Distributing a factor over (1 - pi/4)
-- statement:
--   For every real $a$: $a^2(1-\pi/4) = a^2 - a^2\pi/4$, by distributivity.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_79778`, whose bare `π` is not resolvable under its narrow `Mathlib.Analysis.Complex.Basic` preamble.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_79778 (Apache-2.0).

import Mathlib

theorem WorkbookCorrected.pi_factor_algebra_79778 (a : ℝ) : a^2 * (1 - Real.pi / 4) = a^2 - a^2 * Real.pi / 4 := by sorry
