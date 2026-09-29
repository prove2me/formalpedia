-- Prove2me | Theorems.Thm_lean_workbook_plus_15682
-- name    : lean_workbook_plus_15682
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/b951cb2d-7d05-4c1f-82a2-28ac7d19904e
-- statement:
--   Prove $2^{k+1}>4k+1$ for $k \geq 3$ using induction.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15682 (k : ℕ) (h₁ : 3 ≤ k) : 2 ^ (k + 1) > 4 * k + 1   :=  by sorry
