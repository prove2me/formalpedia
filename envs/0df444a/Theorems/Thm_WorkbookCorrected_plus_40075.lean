-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_40075
-- name    : WorkbookCorrected.plus_40075
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-29T13:34:05.174963+00:00
-- url     : https://prove2.me/theorems/2f636f50-456d-4f92-b757-f5e0ada027ae
-- title:
--   Elementary arithmetic identity #40075
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   2000 + 2001 + 2002 + 2003 + 2004 + 2005 + 2006 = 14021
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_40075`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_40075 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_40075; Apache-2.0; corrects Open node be824db0-65bf-4f2a-9c7f-97815131ff94

import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_40075 : 2000 + 2001 + 2002 + 2003 + 2004 + 2005 + 2006 = 14021 := by sorry
