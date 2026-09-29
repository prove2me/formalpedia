-- Prove2me | Theorems.Thm_lean_workbook_plus_49351
-- name    : lean_workbook_plus_49351
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/aa680ee2-bd2b-4a84-bcfc-d77739a6b3d4
-- statement:
--   Prove that for all positive integers $n$, there exist no integers $m$ such that $(2^{n}-1)(3^{n}-1)=m^{2}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49351 : ∀ n : ℕ, ¬ (∃ m : ℤ, (2^n-1)*(3^n-1) = m^2)   :=  by sorry
