-- Prove2me | Theorems.Thm_lean_workbook_plus_73041
-- name    : lean_workbook_plus_73041
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/7fbff252-0f3b-4642-a182-c884a96987d0
-- statement:
--   Is it $2\sqrt 7 - 4 \le k \le 2$ ?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_73041 (k : ℝ) : 2 * Real.sqrt 7 - 4 ≤ k ∧ k ≤ 2 ↔ ↑2 * Real.sqrt 7 - 4 ≤ k ∧ k ≤ ↑2   :=  by sorry
