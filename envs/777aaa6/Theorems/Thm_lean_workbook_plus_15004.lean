-- Prove2me | Theorems.Thm_lean_workbook_plus_15004
-- name    : lean_workbook_plus_15004
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/5dee9eed-1d13-4ef7-a72c-1b9f839fd47f
-- statement:
--   Let $\mathbb{S}$ be a set of $100$ integers, none of them are greater than $199$ . Prove that there exist $\mathbb{T}\subset \mathbb{S}$ such that product of all elements of $\mathbb{T}$ is a square number.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15004 (s : Finset ℤ) (hs : ∀ x ∈ s, 0 < x ∧ x ≤ 199) : ∃ t ⊆ s, ∃ z : ℤ, t.prod (fun x ↦ x) = z^2   :=  by sorry
