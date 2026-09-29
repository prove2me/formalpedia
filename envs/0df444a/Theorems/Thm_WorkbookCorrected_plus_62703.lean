-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_62703
-- name    : WorkbookCorrected.plus_62703
-- status  : Proved
-- author  : @Rizwan G Mir
-- created : 2026-09-24T19:20:42.425807+00:00
-- url     : https://prove2.me/theorems/749b76ad-1130-469a-b930-d4bfbfcc23b4
-- title:
--   Binomial row sum equals a power of two #62703
-- statement:
--   $\sum_{r=0}^{n} \binom{n}{r} = 2^n$.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_62703`, which used the deprecated `∑ r in s` syntax and bare `choose`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_62703 (Apache-2.0).

import Mathlib

theorem WorkbookCorrected.plus_62703 (n : ℕ) : ∑ r ∈ Finset.range (n+1), Nat.choose n r = 2^n := by sorry
