-- Prove2me | Theorems.Thm_lean_workbook_plus_17933
-- name    : lean_workbook_plus_17933
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/cc0a406d-4554-4da2-97dc-4c0b54ea3f80
-- statement:
--   Let $a+b=1$. Prove that $\dfrac{1}{2}\geq \dfrac{a}{b+2} + \dfrac{b}{a+2}$ for all non-negative reals $a$ and $b$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17933 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) : 1 / 2 ≥ a / (b + 2) + b / (a + 2)   :=  by sorry
