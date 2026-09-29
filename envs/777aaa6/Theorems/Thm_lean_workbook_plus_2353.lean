-- Prove2me | Theorems.Thm_lean_workbook_plus_2353
-- name    : lean_workbook_plus_2353
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/e5721d08-409a-452f-a717-003eb79a299a
-- statement:
--   Sum of $30$ numbers is multiple of $5$ and $6$ , so it is multiple of $30$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2353 {s : ℕ} (h : s ≡ 0 [ZMOD 5]) (h' : s ≡ 0 [ZMOD 6]) : s ≡ 0 [ZMOD 30]   :=  by sorry
