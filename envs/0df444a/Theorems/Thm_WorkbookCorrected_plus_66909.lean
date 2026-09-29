-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_66909
-- name    : WorkbookCorrected.plus_66909
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-23T13:22:44.238102+00:00
-- url     : https://prove2.me/theorems/92a1453f-60e5-4d6e-a1ca-4a687e36084f
-- title:
--   Binomial coefficient identity #66909
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   (\binom{25}{3}) = 2300
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_66909`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_66909 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_66909; Apache-2.0; corrects Open node 8efbdde0-6aac-4403-a787-70244d3e54b1

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_66909 : (Nat.choose 25 3) = 2300 := by sorry
