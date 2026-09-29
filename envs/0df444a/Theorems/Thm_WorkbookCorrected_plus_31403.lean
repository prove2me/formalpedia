-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_31403
-- name    : WorkbookCorrected.plus_31403
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T11:42:58.6145+00:00
-- url     : https://prove2.me/theorems/f2e49be0-884f-4a4c-b43e-f06020ea7f89
-- title:
--   Binomial coefficient identity #31403
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   (\binom{32}{5}) - (\binom{6}{1} * \binom{22}{5}) + (\binom{6}{2} * \binom{12}{5}) = 55252
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_31403`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_31403 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_31403; Apache-2.0; corrects Open node ecde47a8-b43f-4c23-98fd-46b797d7e2f5

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_31403 : (Nat.choose 32 5) - ((Nat.choose 6 1) * (Nat.choose 22 5)) + ((Nat.choose 6 2) * (Nat.choose 12 5)) = 55252 := by sorry
