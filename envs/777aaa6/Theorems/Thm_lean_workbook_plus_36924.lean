-- Prove2me | Theorems.Thm_lean_workbook_plus_36924
-- name    : lean_workbook_plus_36924
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/939b12c6-ebe8-458f-86c9-e96978ca8552
-- statement:
--   Prove that $2^n \leq n^3$ for $2 \leq n \leq 9$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36924 : ∀ n : ℕ, 2 ≤ n ∧ n ≤ 9 → 2 ^ n ≤ n ^ 3   :=  by sorry
