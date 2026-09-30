-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_48990
-- name    : WorkbookCorrected.plus_48990
-- status  : Disproved
-- author  : @carlok
-- created : 2026-09-29T19:11:51.24712+00:00
-- url     : https://prove2.me/theorems/f99db012-dac2-49e4-95ac-5460abf468f9
-- title:
--   Binomial coefficient identity #48990
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   (choose (16 + 3) 3 - choose (11 + 3) 3 - choose (10 + 3) 3 - 2 * choose (9 + 3) 3 + choose (5 + 3) 3 + 2 * choose (4 + 3) 3 + 2 * choose (3 + 3) 3 + choose (2 + 3) 3) = 55
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_48990`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_48990 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_48990; Apache-2.0; corrects Open node c1b09ea6-7631-4bce-a57e-05fb3c48a4c9

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_48990 : ((Nat.choose (16 + 3) 3) - (Nat.choose (11 + 3) 3) - (Nat.choose (10 + 3) 3) - 2 * (Nat.choose (9 + 3) 3) + (Nat.choose (5 + 3) 3) + 2 * (Nat.choose (4 + 3) 3) + 2 * (Nat.choose (3 + 3) 3) + (Nat.choose (2 + 3) 3)) = 55 := by sorry
