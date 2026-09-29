-- Prove2me | Theorems.Thm_lean_workbook_plus_52854
-- name    : lean_workbook_plus_52854
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/fc381194-fb71-41cf-be5b-be621cb4bc58
-- statement:
--   How about $a_n=\begin{cases}1 & n=k! \text{ for some } k\in \mathbb{N} \ 1/n^2 & \text{otherwise}\end{cases}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52854 : ∀ n : ℕ, (∃ k : ℕ, n = k! → a_n = 1) ∨ (∀ k : ℕ, n ≠ k! → a_n = 1 / n ^ 2)   :=  by sorry
