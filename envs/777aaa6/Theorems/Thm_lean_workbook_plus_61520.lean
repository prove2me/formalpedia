-- Prove2me | Theorems.Thm_lean_workbook_plus_61520
-- name    : lean_workbook_plus_61520
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/4c81187e-f633-4a78-8a92-ef71ee57e22a
-- statement:
--   Let $a,b,c$ be positive numbers with $a^2+b^2+c^2=3$. Prove that $a+b+c\ge 3\sqrt{3}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61520 : ∀ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 ∧ a^2 + b^2 + c^2 = 3 → a + b + c ≥ 3 * Real.sqrt 3   :=  by sorry
