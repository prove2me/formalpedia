-- Prove2me | Theorems.Thm_lean_workbook_plus_81229
-- name    : lean_workbook_plus_81229
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/8175fd76-5b82-4332-895e-ac6a9e14566f
-- statement:
--   The Chan Shun Auditorium at UC Berkeley has room number $2050$ . The number of seats in the auditorium is a factor of the room number, and there are between $150$ and $431$ seats, inclusive. What is the sum of all of the possible numbers of seats in Chan Shun Auditorium?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81229 (n : ℕ) (h₁ : 150 ≤ n) (h₂ : n ≤ 431) (h₃ : n ∣ 2050) : ∑ k in Finset.filter (λ x => x ∣ 2050) (Finset.Icc 150 431), k = 615   :=  by sorry
