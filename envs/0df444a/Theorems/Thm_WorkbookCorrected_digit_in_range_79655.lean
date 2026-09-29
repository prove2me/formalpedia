-- Prove2me | Theorems.Thm_WorkbookCorrected_digit_in_range_79655
-- name    : WorkbookCorrected.digit_in_range_79655
-- status  : Proved
-- author  : @Rizwan G Mir
-- created : 2026-09-24T19:43:49.512224+00:00
-- url     : https://prove2.me/theorems/ded52e47-f4cb-46a7-9496-9be37a1718a0
-- title:
--   Every number in [101,2001] has a digit in [0,9]
-- statement:
--   For every $x \in [101,2001]$, some digit of the base-10 representation of $x$ lies in $[0,9]$ — true since every base-10 digit is automatically in $[0,9]$.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_79655` (same statement, republished with a working preamble).
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_79655 (Apache-2.0).

import Mathlib

theorem WorkbookCorrected.digit_in_range_79655 : ∀ x ∈ Finset.Icc 101 2001, ∃ y ∈ Finset.Icc 0 9, y ∈ (Nat.digits 10 x) := by sorry
