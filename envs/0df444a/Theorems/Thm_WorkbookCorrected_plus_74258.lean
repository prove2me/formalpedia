-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_74258
-- name    : WorkbookCorrected.plus_74258
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T08:25:00.346545+00:00
-- url     : https://prove2.me/theorems/9ed0e2d0-dd36-44e1-9749-8db54756715c
-- title:
--   Binomial one hundred five choose two
-- statement:
--   The binomial coefficient evaluation
--   $$
--   \binom{105}{2}=5460
--   $$
--   holds in the natural numbers.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_74258`, which used a preamble of only `Mathlib.Analysis.Complex.Basic` (and, where relevant, non-compiling notation such as bare `φ`).
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_74258 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_74258; Apache-2.0; corrects Open node 89873379-8954-4df5-9f5e-5fd42012e9ad

import Mathlib.Data.Nat.Choose.Basic

theorem WorkbookCorrected.plus_74258 : Nat.choose 105 2 = 5460 := by sorry
