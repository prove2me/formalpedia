-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_55641
-- name    : WorkbookCorrected.plus_55641
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-29T12:38:03.379393+00:00
-- url     : https://prove2.me/theorems/3f7f7393-38d2-4f5a-af4f-42e0ef4d818b
-- title:
--   Binomial-factorial identity #55641
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   (7! * 4! * 70) = (7! * 4! * choose (4+5-1) (5-1))
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_55641`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_55641 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_55641; Apache-2.0; corrects Open node 25320e62-d1a0-4054-9dfc-9abcb2037f40

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_55641 : ((Nat.factorial 7) * (Nat.factorial 4) * 70) = ((Nat.factorial 7) * (Nat.factorial 4) * (Nat.choose (4+5-1) (5-1))) := by sorry
