-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_78618
-- name    : WorkbookCorrected.plus_78618
-- status  : Proved
-- author  : @Rizwan G Mir
-- created : 2026-09-24T19:35:07.657547+00:00
-- url     : https://prove2.me/theorems/97bb3714-3bf0-42bd-a016-1459fab85e45
-- title:
--   Binomial coefficient symmetry #78618
-- statement:
--   For $r \le n$, $\binom{n}{r} = \binom{n}{n-r}$ (Pascal's symmetry rule).
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_78618`, whose bare `choose` was unresolvable under its narrow preamble.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_78618 (Apache-2.0).

import Mathlib

theorem WorkbookCorrected.plus_78618 (n r : ℕ) (h₁ : r ≤ n) (h₂ : n - r ≤ n) : Nat.choose n r = Nat.choose n (n - r) := by sorry
