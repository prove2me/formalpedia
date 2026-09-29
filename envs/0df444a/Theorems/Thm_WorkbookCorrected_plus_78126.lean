-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_78126
-- name    : WorkbookCorrected.plus_78126
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-17T19:14:45.298399+00:00
-- url     : https://prove2.me/theorems/37ef585b-cb91-4457-8ff7-f70c521ec0c5
-- statement:
--   The binomial coefficient identity $\binom{12}{5} = 792$.
--
--   Formalization Note: Corrected missing colon in Lean-Workbook record `lean_workbook_plus_78126`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_78126 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_78126; Apache-2.0; corrects Open node 6d8c3ed9-e461-402d-a290-b7a753818b14

import Mathlib.Data.Nat.Choose.Basic

theorem WorkbookCorrected.plus_78126 : Nat.choose 12 5 = 792 := by sorry
