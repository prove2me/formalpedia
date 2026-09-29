-- Prove2me | Theorems.Thm_lean_workbook_plus_81286
-- name    : lean_workbook_plus_81286
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/6433aee1-c300-425b-9337-001a969cd1d3
-- statement:
--   Prove that there is no perfect square between $n^2$ and $(n+1)^2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81286 (n : ℕ) : ¬ ∃ k : ℕ, n^2 < k^2 ∧ k^2 < (n + 1)^2   :=  by sorry
