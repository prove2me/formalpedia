-- Prove2me | Theorems.Thm_lean_workbook_plus_5630
-- name    : lean_workbook_plus_5630
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/e04a5397-773b-4c56-894e-3562a92e5468
-- statement:
--   Prove that for any sets A, B, and C, $(A \cup C) \setminus B \subseteq (A \setminus B) \cup C$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_5630 (A B C : Set α) : (A ∪ C) \ B ⊆ (A \ B) ∪ C   :=  by sorry
