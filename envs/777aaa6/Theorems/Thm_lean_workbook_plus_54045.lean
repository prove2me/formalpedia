-- Prove2me | Theorems.Thm_lean_workbook_plus_54045
-- name    : lean_workbook_plus_54045
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/d3940430-9153-405a-8a9b-16ea161f45f3
-- statement:
--   Derive the equation $2k^2-r^2=1$ from the given equations $n+1=k^2$ and $2n+1=r^2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54045 (n k r : ℕ) (h₁ : n + 1 = k^2) (h₂ : 2 * n + 1 = r^2) : 2 * k^2 - r^2 = 1   :=  by sorry
