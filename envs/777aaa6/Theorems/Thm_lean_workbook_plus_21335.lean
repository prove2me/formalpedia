-- Prove2me | Theorems.Thm_lean_workbook_plus_21335
-- name    : lean_workbook_plus_21335
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/f46b876c-95f3-41b0-b4d6-754437d465b0
-- statement:
--   Prove that $\frac{ab}{a+b}+ \frac{bc}{b+c} \le \frac{(a+b)(b+c)}{(a+b)+(b+c)}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21335 : ∀ a b c : ℝ, (a * b) / (a + b) + (b * c) / (b + c) ≤ (a + b) * (b + c) / (a + b + (b + c))   :=  by sorry
