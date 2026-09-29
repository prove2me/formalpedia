-- Prove2me | Theorems.Thm_lean_workbook_plus_3121
-- name    : lean_workbook_plus_3121
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/d8bf9e24-d293-4827-80c9-1d69e9d45a65
-- statement:
--   Prove $ n(n-1) = 2 \cdot \binom{n}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3121 (n : ℕ) : n * (n - 1) = 2 * choose n 2   :=  by sorry
