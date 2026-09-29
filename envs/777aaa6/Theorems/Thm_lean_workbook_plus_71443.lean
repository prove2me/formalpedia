-- Prove2me | Theorems.Thm_lean_workbook_plus_71443
-- name    : lean_workbook_plus_71443
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/5427ed3e-713a-4ad2-a75b-9f2af3261078
-- statement:
--   Given a real number $\alpha >0$ . Prove there exists a $n$ such that $\lfloor n^2\alpha \rfloor$ is even.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71443 (α : ℝ) (h : α > 0) : ∃ n : ℕ, Even (Int.floor (n^2 * α))   :=  by sorry
