-- Prove2me | Theorems.Thm_lean_workbook_plus_48859
-- name    : lean_workbook_plus_48859
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/25cc6d55-9e2a-4b9f-924f-6af3194b9ca5
-- statement:
--   With $x_1=21$ , $x_2=17$ , $x_3=16$ , $x_4=14$ , again with $x_1^2$ , $x_2^2$ , $x_3^2$ , $x_4^2$ being the sides of a quadrilateral, gives $4(\frac{x_{1}}{x_{2}}+\frac{x_{2}}{x_{3}}+\frac{x_{3}}{x_{4}}+\frac{x_{4}}{x_{1}}) - (x_{1}+x_{2}+x_{3}+x_{4})(\frac{1}{x_{1}}+\frac{1}{x_{2}}+\frac{1}{x_{3}}+\frac{1}{x_{4}}) =\frac{10}{119}>0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_48859 (x : ℕ → ℕ) (hx : x 1 = 21 ∧ x 2 = 17 ∧ x 3 = 16 ∧ x 4 = 14) : 4 * (x 1 / x 2 + x 2 / x 3 + x 3 / x 4 + x 4 / x 1) - (x 1 + x 2 + x 3 + x 4) * (1 / x 1 + 1 / x 2 + 1 / x 3 + 1 / x 4) = 10 / 119   :=  by sorry
