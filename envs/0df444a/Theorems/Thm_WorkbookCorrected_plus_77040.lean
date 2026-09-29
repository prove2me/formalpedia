-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_77040
-- name    : WorkbookCorrected.plus_77040
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T08:18:30.264088+00:00
-- url     : https://prove2.me/theorems/71761591-0874-4a90-9a91-eecd9a37f246
-- title:
--   Seven hundred fifty minus five hundred thirty-six
-- statement:
--   In the natural numbers one has the difference identity $750-536=214$.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_77040`, which omitted the colon after the theorem name and used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_77040 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_77040; Apache-2.0; corrects Open node 3907cb4e-21d7-43bb-87e0-40472e382d0b

import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_77040 : (750 : ℕ) - 536 = 214 := by sorry
