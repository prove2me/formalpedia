-- Prove2me | Theorems.Thm_lean_workbook_plus_19564
-- name    : lean_workbook_plus_19564
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/fac97896-5e24-4cae-a2fd-2d27c307c453
-- statement:
--   Evaluate: $\frac{1}{1\cdot 2 \cdot 3}+\frac{2}{2\cdot 3 \cdot 4}+\frac{3}{3\cdot 4 \cdot 5}+...+\frac{98}{98 \cdot 99 \cdot 100}$ . Express your answer as a fraction in simplest form $\frac{b}{a}$ . Find $a+b$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19564 (a b : ℕ) (hab : a = 49 ∧ b = 100) : (∑ k in Finset.Icc 1 98, (k + 1) / (k * (k + 1) * (k + 2))) = b / a ∧ a + b = 149   :=  by sorry
