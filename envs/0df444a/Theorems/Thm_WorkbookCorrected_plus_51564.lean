-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_51564
-- name    : WorkbookCorrected.plus_51564
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T08:14:23.602206+00:00
-- url     : https://prove2.me/theorems/6313d738-b65f-43ff-9157-0bad1c80b507
-- title:
--   Binomial choose n 0 equals 1
-- statement:
--   For every natural number $n$, the binomial coefficient satisfies $\binom{n}{0}=1$: there is exactly one way to choose an empty subset.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_51564`, which used bare `choose` under a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_51564 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_51564; Apache-2.0; corrects Open node eed219fd-9fe2-4c1d-bdc9-5bbdeda0f160

import Mathlib.Data.Nat.Choose.Basic

theorem WorkbookCorrected.plus_51564 (n : ℕ) : Nat.choose n 0 = 1 := by sorry
