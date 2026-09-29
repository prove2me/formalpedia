-- Prove2me | Theorems.Thm_lean_workbook_plus_4307
-- name    : lean_workbook_plus_4307
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/6652ab65-40d3-4450-9b91-351e4234b8de
-- statement:
--   Inequality 2:\nBy Cauchy Schwarz $\sum \frac{4a}{b+c}\leq \sum (\frac{a}{b}+\frac{a}{c})\Rightarrow$ we need to prove: \n\n $\frac{a^3+b^3+c^3}{abc}\geq \frac{a}{b}+\frac{b}{c}+\frac{c}{a}\Leftrightarrow a^3+b^3+c^3\geq a^2c+b^2a+c^2b$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4307 : ∀ a b c : ℝ, a * b * c > 0 → a^3 + b^3 + c^3 ≥ a^2 * c + b^2 * a + c^2 * b   :=  by sorry
