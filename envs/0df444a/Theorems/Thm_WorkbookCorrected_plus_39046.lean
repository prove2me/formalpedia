-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_39046
-- name    : WorkbookCorrected.plus_39046
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T08:47:22.699091+00:00
-- url     : https://prove2.me/theorems/536968da-f9ad-4219-b1d0-c01a5c855988
-- title:
--   Nine factorial over mixed factorials
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   \frac{9!}{2!\,2!\,4!} = 3780
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_39046`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_39046 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_39046; Apache-2.0; corrects Open node 42c8db8f-c49c-4431-9e87-93e95dfeae63

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_39046 : Nat.factorial 9 / (Nat.factorial 2 * Nat.factorial 2 * Nat.factorial 4) = 3780 := by sorry
