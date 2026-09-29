-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_69069
-- name    : WorkbookCorrected.plus_69069
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T08:24:55.110148+00:00
-- url     : https://prove2.me/theorems/990d92d7-0296-4e6e-948f-36d3845365f6
-- title:
--   Inclusion-exclusion chocolate count 1560
-- statement:
--   The binomial inclusion-exclusion count
--   $$
--   4^{6}-\binom{4}{3}\cdot 3^{6}+\binom{4}{2}\cdot 2^{6}-\binom{4}{1}\cdot 1^{6}=1560
--   $$
--   holds as an identity of natural numbers.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_69069`, which omitted the colon after the theorem name and used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_69069 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_69069; Apache-2.0; corrects Open node 5e012bad-a5f1-465c-ac40-ce00d533139e

import Mathlib.Data.Nat.Choose.Basic

theorem WorkbookCorrected.plus_69069 : 4 ^ 6 - (Nat.choose 4 3 * 3 ^ 6) + (Nat.choose 4 2 * 2 ^ 6) - (Nat.choose 4 1 * 1 ^ 6) = 1560 := by sorry
