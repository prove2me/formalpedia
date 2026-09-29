-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_30985
-- name    : WorkbookCorrected.plus_30985
-- status  : Proved
-- author  : @Rizwan G Mir
-- created : 2026-09-24T19:20:35.911379+00:00
-- url     : https://prove2.me/theorems/1e5b576c-7e0e-455f-a10f-61ed1654ba90
-- title:
--   Pascal's rule, degree one #30985
-- statement:
--   For every natural $n$, $\binom{n}{0} + \binom{n}{1} = \binom{n+1}{1}$.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_30985`, whose bare `choose` and untyped binder `n` were unresolvable/malformed under its narrow preamble.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_30985 (Apache-2.0).

import Mathlib

theorem WorkbookCorrected.plus_30985 : ∀ n : ℕ, Nat.choose n 0 + Nat.choose n 1 = Nat.choose (n + 1) 1 := by sorry
