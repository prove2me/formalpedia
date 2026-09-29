-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_59236
-- name    : WorkbookCorrected.plus_59236
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T08:28:42.834537+00:00
-- url     : https://prove2.me/theorems/c80b8fe5-b3cb-4a29-ba9a-7697d6ab99c2
-- title:
--   Binomial coefficient C(4,2) equals 6
-- statement:
--   The elementary natural-number identity
--   $$
--   \binom{4}{2}=6
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_59236`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_59236 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_59236; Apache-2.0; corrects Open node c1bf05d1-ccef-4905-9631-c171df6c7335

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_59236 : Nat.choose 4 2 = 6 := by sorry
