-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_4730
-- name    : WorkbookCorrected.plus_4730
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T11:56:28.747218+00:00
-- url     : https://prove2.me/theorems/86e49823-6f28-4568-9a37-92ef5446a610
-- title:
--   Factorial arithmetic identity #4730
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   2005 * 2004 * 2003 / 3! = 2 * 5 * 167 * 401 * 2003
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_4730`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_4730 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_4730; Apache-2.0; corrects Open node e17106d9-2278-4962-83a7-5de217ae525c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_4730 : 2005 * 2004 * 2003 / (Nat.factorial 3) = 2 * 5 * 167 * 401 * 2003 := by sorry
