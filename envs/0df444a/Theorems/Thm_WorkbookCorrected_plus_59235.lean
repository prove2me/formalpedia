-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_59235
-- name    : WorkbookCorrected.plus_59235
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-23T13:22:48.984068+00:00
-- url     : https://prove2.me/theorems/55b18b88-310e-4591-b867-0cf671e30703
-- title:
--   Binomial coefficient identity #59235
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   (\binom{49}{2}) = 1176
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_59235`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_59235 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_59235; Apache-2.0; corrects Open node 01fa7257-0b46-4ef2-b909-6ff9508dd4d4

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_59235 : (Nat.choose 49 2) = 1176 := by sorry
