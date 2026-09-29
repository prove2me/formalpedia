-- Prove2me | Theorems.Thm_lean_workbook_plus_81029
-- name    : lean_workbook_plus_81029
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/972bf755-ab59-4fad-99cc-092adc23f0f4
-- statement:
--   we know that there is an $x$ s.t. $p^k|x^{p-1}-1$ (we can construct such solutions by induction on $k$ , for example)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81029 (p k : ℕ) : ∃ x : ℕ, p ^ k ∣ x ^ (p - 1) - 1   :=  by sorry
