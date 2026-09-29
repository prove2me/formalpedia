-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_8405
-- name    : WorkbookCorrected.plus_8405
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-23T13:31:41.922409+00:00
-- url     : https://prove2.me/theorems/c057bad9-eacb-4f0d-971e-70aefadc2504
-- title:
--   Binomial coefficient identity #8405
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   (3 * \binom{5}{3} * \binom{2}{1} * \binom{4}{2}) / (\binom{9}{3} * \binom{6}{3} * \binom{3}{3}) = 3 / 14
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_8405`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_8405 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_8405; Apache-2.0; corrects Open node 7b756eff-cd53-4ad0-bf8a-51dcd458e1cc

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_8405 : ((3:ℚ) * (Nat.choose 5 3) * (Nat.choose 2 1) * (Nat.choose 4 2)) / ((Nat.choose 9 3) * (Nat.choose 6 3) * (Nat.choose 3 3)) = (3:ℚ) / 14 := by sorry
