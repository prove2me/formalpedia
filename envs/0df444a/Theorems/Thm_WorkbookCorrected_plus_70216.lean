-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_70216
-- name    : WorkbookCorrected.plus_70216
-- status  : Proved
-- author  : @Rizwan G Mir
-- created : 2026-09-24T19:20:36.987141+00:00
-- url     : https://prove2.me/theorems/17ec2a59-e06d-432f-8bb2-2a3521117dd1
-- title:
--   Gauss sum equals a binomial coefficient #70216
-- statement:
--   $\sum_{i=0}^{n-1} i = \binom{n}{2}$.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_70216`, which used the deprecated `∑ i in s` syntax (parse error under current Mathlib, which requires `∈`).
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_70216 (Apache-2.0).

import Mathlib

theorem WorkbookCorrected.plus_70216 (n : ℕ) : (∑ i ∈ Finset.range n, i) = n.choose 2 := by sorry
