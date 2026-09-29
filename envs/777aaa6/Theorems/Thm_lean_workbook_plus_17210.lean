-- Prove2me | Theorems.Thm_lean_workbook_plus_17210
-- name    : lean_workbook_plus_17210
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/febaf319-4bc4-4a6b-bf82-b079f9cb3e0a
-- statement:
--   Show that for all prime numbers $p$ , $Q(p)=\prod^{p-1}_{k=1}k^{2k-p-1}$ is an integer.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17210 (p : ℕ) (hp : p.Prime) : ∃ k : ℕ, (∏ k in Finset.Ico 1 (p-1), k ^ (2 * k - p - 1) : ℚ) = k   :=  by sorry
