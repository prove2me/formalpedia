-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_69256
-- name    : WorkbookCorrected.plus_69256
-- status  : Proved
-- author  : @Rizwan G Mir
-- created : 2026-09-24T19:35:07.041201+00:00
-- url     : https://prove2.me/theorems/70c69e35-b0fa-4f29-bc8d-adac4908844d
-- title:
--   Hockey-stick identity, diagonal form #69256
-- statement:
--   $\sum_{k=0}^{m} \binom{n+k}{k} = \binom{n+m+1}{m}$ — the hockey-stick identity in its diagonal form (same identity as `WorkbookCorrected.plus_36538`, restated with the bound variable named $m$).
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_69256`, whose bare `choose` was unresolvable under its narrow preamble.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_69256 (Apache-2.0).

import Mathlib

theorem WorkbookCorrected.plus_69256 (n m : ℕ) : ∑ k ∈ Finset.range (m+1), Nat.choose (n + k) k = Nat.choose (n + m + 1) m := by sorry
