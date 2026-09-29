-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_36538
-- name    : WorkbookCorrected.plus_36538
-- status  : Proved
-- author  : @Rizwan G Mir
-- created : 2026-09-24T19:35:06.688857+00:00
-- url     : https://prove2.me/theorems/89f5da31-aff2-4927-a128-6271bf91a259
-- title:
--   Hockey-stick identity, diagonal form #36538
-- statement:
--   $\sum_{k=0}^{r} \binom{n+k}{k} = \binom{n+r+1}{r}$ — the hockey-stick identity in its diagonal form.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_36538`, whose bare `choose` was unresolvable under its narrow preamble.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_36538 (Apache-2.0).

import Mathlib

theorem WorkbookCorrected.plus_36538 (n r : ℕ) : ∑ k ∈ Finset.range (r + 1), Nat.choose (n + k) k = Nat.choose (n + r + 1) r := by sorry
