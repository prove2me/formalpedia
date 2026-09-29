-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_29982
-- name    : WorkbookCorrected.plus_29982
-- status  : Proved
-- author  : @Rizwan G Mir
-- created : 2026-09-24T19:20:33.395655+00:00
-- url     : https://prove2.me/theorems/0e164694-6eb6-423a-9299-9ca667842842
-- title:
--   Binomial coefficient symmetry #29982
-- statement:
--   For $n \ge r$, $\binom{n}{r} = \binom{n}{n-r}$ (Pascal's symmetry rule).
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_29982`, whose bare `choose` was unresolvable under its narrow preamble.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_29982 (Apache-2.0).

import Mathlib

theorem WorkbookCorrected.plus_29982 (n r : ℕ) (h₁ : n ≥ r) : Nat.choose n r = Nat.choose n (n - r) := by sorry
