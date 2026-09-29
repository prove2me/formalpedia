-- Prove2me | Theorems.Thm_lean_workbook_plus_75403
-- name    : lean_workbook_plus_75403
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/ef777cb9-6944-41d7-aab9-303451ab8f31
-- statement:
--   Let $ a$ and $ b$ be two real numbers such that $ a\le b$ . Prove that $ \bigcap_{n\in N^{*}}[a-\frac{1}{n},b+\frac{1}{n}]=[a,b]$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75403 (a b : ℝ) (h : a ≤ b) :
  ⋂ (n : ℕ), (Set.Icc (a - 1 / n) (b + 1 / n)) = Set.Icc a b   :=  by sorry
