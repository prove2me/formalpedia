-- Prove2me | Theorems.Thm_lean_workbook_plus_62290
-- name    : lean_workbook_plus_62290
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/436c0b6a-4e0e-42c6-84ea-6ad8811e0e71
-- statement:
--   Find the number of real solution of the system\n$\{\begin{array}{l} [ \ x ]+\{ y\}=[\ y] \{x \} \ x+y=n \end{array}$\nwhere $[\ x]$ is the floor part, $\{x \}$ is the fractional part, $n \in N$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62290 (n : ℕ) : { x : ℝ | (↑⌊x⌋ + ⌊y⌋ = ⌊y⌋ * ⌊x⌋ ∧ x + y = n) } = { x : ℝ | (⌊x⌋ + ⌊y⌋ = ⌊y⌋ * ⌊x⌋ ∧ x + y = n) }   :=  by sorry
