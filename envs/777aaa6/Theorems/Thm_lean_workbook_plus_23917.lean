-- Prove2me | Theorems.Thm_lean_workbook_plus_23917
-- name    : lean_workbook_plus_23917
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/57f814a2-82ae-4e63-a525-3749d5e9c557
-- statement:
--   By the hypothesis,a+b+c=2,and by C-S $\frac{1}{3}\left ( a+b+c \right )^{2}\geq ab+bc+ca\Rightarrow \sum bc\leq \frac{4}{3}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23917  (a b c : ℝ)
  (h₀ : a + b + c = 2) :
  1 / 3 * (a + b + c)^2 ≥ a * b + b * c + c * a → a * b + b * c + c * a ≤ 4 / 3   :=  by sorry
