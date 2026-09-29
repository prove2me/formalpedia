-- Prove2me | Theorems.Thm_lean_workbook_plus_23691
-- name    : lean_workbook_plus_23691
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/fd5b3d59-22dd-4c7e-9b39-0d8a21b03f74
-- statement:
--   Let $A$ be a set, and suppose $x \notin A$ . Describe $P(A \cup \{x\})$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23691 (A : Set α) (x : α) (hx : x ∉ A) : 𝒫 (A ∪ {x}) = 𝒫 A ∪ {B | B ⊆ A ∧ x ∈ B}   :=  by sorry
