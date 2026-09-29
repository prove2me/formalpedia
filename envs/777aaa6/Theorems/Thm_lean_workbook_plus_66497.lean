-- Prove2me | Theorems.Thm_lean_workbook_plus_66497
-- name    : lean_workbook_plus_66497
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/823fc7da-7ec7-4bdb-afd4-181e1958db9b
-- statement:
--   Let $a \in R$ s.t. $0\leq a\leq \frac{1}{n}\forall n \in Z^{+}$ then $a=0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66497 (a : ℝ) (h : ∀ n : ℕ, 0 ≤ a ∧ a ≤ 1 / n) : a = 0   :=  by sorry
