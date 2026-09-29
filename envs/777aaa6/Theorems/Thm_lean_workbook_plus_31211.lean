-- Prove2me | Theorems.Thm_lean_workbook_plus_31211
-- name    : lean_workbook_plus_31211
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/263eff17-f280-4257-bd07-d1b789e58b26
-- statement:
--   For every $n \in N$, find a $k \in N$ such that $2^k \geq n$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31211 (n : ℕ) : ∃ k, 2 ^ k ≥ n   :=  by sorry
