-- Prove2me | Theorems.Thm_lean_workbook_plus_63384
-- name    : lean_workbook_plus_63384
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/01016c23-9ecf-4685-b7d6-6c05388e266a
-- statement:
--   Given any integer $G>13$ , there exist distinct integers $x_i>0$ such that $G^3=\sum_{i=1}^5x_i^3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63384 (G : ℤ) (hG : 13 < G) : ∃ x : ℕ → ℤ, (∀ i : ℕ, 0 < i ∧ x i ≠ x j) ∧ G^3 = ∑ i in Finset.range 5, (x i)^3   :=  by sorry
