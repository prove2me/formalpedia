-- Prove2me | Theorems.Thm_lean_workbook_plus_44537
-- name    : lean_workbook_plus_44537
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/bd7531a2-e8ad-47de-9b6b-fd4280c6967d
-- statement:
--   For $n=3$, we have $1 \times 3 + 2 \times 2 + 3 \times 1 = 10$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44537 (n : ℕ) (h : n = 3) : 1 * n + 2 * (n-1) + 3 * (n-2) = 10   :=  by sorry
