-- Prove2me | Theorems.Thm_lean_workbook_plus_24744
-- name    : lean_workbook_plus_24744
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/83699190-3e9b-4343-8785-645ab501b097
-- statement:
--   Prove or disprove: $ \left \lceil x+n \right \rceil = \left \lceil x \right \rceil + n$ for all $x \in \mathbb{R}$ and $n \in \mathbb{Z}$, where $\lceil \cdot \rceil$ is the ceiling function.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24744 : ∀ x : ℝ, ∀ n : ℤ, (Int.ceil (x + n) = Int.ceil x + n)   :=  by sorry
