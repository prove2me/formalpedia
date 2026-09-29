-- Prove2me | Theorems.Thm_lean_workbook_plus_20128
-- name    : lean_workbook_plus_20128
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/118f2e11-b0cc-4bec-87dc-d084636521e4
-- statement:
--   If $m$ is even, then $m^2-1 | 3^m + 5^m$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20128 : ∀ m : ℕ, Even m → m^2 - 1 ∣ 3^m + 5^m   :=  by sorry
