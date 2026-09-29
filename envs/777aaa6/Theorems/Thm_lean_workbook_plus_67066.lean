-- Prove2me | Theorems.Thm_lean_workbook_plus_67066
-- name    : lean_workbook_plus_67066
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/50d9547e-0831-4145-b5c0-2b6692bd842f
-- statement:
--   If $m|n$ , we have $2^m -1 | 2^n-1$ ,
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_67066 {m n : ℕ} (hmn: m ∣ n) : 2^m - 1 ∣ 2^n - 1   :=  by sorry
