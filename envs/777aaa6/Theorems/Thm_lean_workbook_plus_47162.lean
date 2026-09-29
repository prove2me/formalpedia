-- Prove2me | Theorems.Thm_lean_workbook_plus_47162
-- name    : lean_workbook_plus_47162
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/867d00c7-cb95-4f5e-a47c-aa357accdc85
-- statement:
--   Transform the given recurrence into $a_{n+1}=a_n+\frac{1}{n}$ which clearly yields $a_{n}=1+\sum_{i=1}^{n}\frac{1}{i}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47162 (a : ℕ → ℝ) (a0 : a 0 = 1) (a_rec : ∀ n, a (n + 1) = a n + 1 / (n + 1)) : ∀ n, a n = 1 + ∑ i in Finset.range n, (1 / (i + 1))   :=  by sorry
