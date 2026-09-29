-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_68927
-- name    : WorkbookCorrected.plus_68927
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T08:24:56.128805+00:00
-- url     : https://prove2.me/theorems/277b4d6d-46e7-43d0-8573-7e12c4b6d11d
-- title:
--   Binomial forty-seven choose two
-- statement:
--   The binomial coefficient evaluation
--   $$
--   \binom{52-5}{2}=\binom{47}{2}=1081
--   $$
--   holds in the natural numbers.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_68927`, which used a preamble of only `Mathlib.Analysis.Complex.Basic` (and, where relevant, non-compiling notation such as bare `φ`).
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_68927 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_68927; Apache-2.0; corrects Open node 638b5d2f-2049-4bf8-b2cf-a5cfcaaac129

import Mathlib.Data.Nat.Choose.Basic

theorem WorkbookCorrected.plus_68927 : Nat.choose (52 - 5) 2 = 1081 := by sorry
