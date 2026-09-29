-- Prove2me | Theorems.Thm_lean_workbook_plus_6872
-- name    : lean_workbook_plus_6872
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/4837e320-b1bb-42f5-9e6d-b570cd393c29
-- statement:
--   Prove that for all $ k > 1 $, $ 3^{k-1} > k $.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6872 (k : ℕ) (h₁ : 1 < k) : 3 ^ (k - 1) > k   :=  by sorry
