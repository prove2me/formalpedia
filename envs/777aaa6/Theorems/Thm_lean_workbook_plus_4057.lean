-- Prove2me | Theorems.Thm_lean_workbook_plus_4057
-- name    : lean_workbook_plus_4057
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/4dc6b93f-33de-4ecc-adab-6da6a6b8c50e
-- statement:
--   Prove that $ \frac{a}{2a+1}+\frac{b}{2b+1}+\frac{c}{2c+1}\geq 1$ given $a,b,c \ge 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4057 (a b c : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) : (a / (2 * a + 1) + b / (2 * b + 1) + c / (2 * c + 1)) ≥ 1   :=  by sorry
