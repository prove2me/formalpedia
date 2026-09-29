-- Prove2me | Theorems.Thm_lean_workbook_plus_82052
-- name    : lean_workbook_plus_82052
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/d587cafe-1060-4aba-9ec5-49ba8af4d169
-- statement:
--   Prove that $\sum_{cyc} \frac{1}{a^2+3} \leq \frac{3}{4}$ for positive numbers $a$, $b$, and $c$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_82052 : ∀ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 → 1 / (a ^ 2 + 3) + 1 / (b ^ 2 + 3) + 1 / (c ^ 2 + 3) ≤ 3 / 4   :=  by sorry
