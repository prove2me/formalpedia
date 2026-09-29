-- Prove2me | Theorems.Thm_lean_workbook_plus_76741
-- name    : lean_workbook_plus_76741
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/26f2e2b2-db3a-4656-bca7-bc00b3e2bc89
-- statement:
--   Let $a,b\geq 0$ and $2a+ b\leq 3.$ Prove that\n$-3\leq a-b+ab \leq \frac{3}{2}$\n$-6\leq a-2b+3ab\leq \frac{13}{6}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_76741 (a b : ℝ) (h₁ : 0 ≤ a) (h₂ : 0 ≤ b) (h₃ : 2 * a + b ≤ 3) : -3 ≤ a - b + a * b ∧ a - b + a * b ≤ 3 / 2   :=  by sorry
