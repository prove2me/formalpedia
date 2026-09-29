-- Prove2me | Theorems.Thm_lean_workbook_plus_73765
-- name    : lean_workbook_plus_73765
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/6e3ae7b6-62a9-49bd-8349-1629c981e309
-- statement:
--   Prove that $0\le n(3n(n+1)-1) $ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_73765 (n : ℕ) : 0 ≤ n * (3 * n * (n + 1) - 1)   :=  by sorry
