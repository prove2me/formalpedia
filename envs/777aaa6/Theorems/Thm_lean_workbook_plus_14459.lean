-- Prove2me | Theorems.Thm_lean_workbook_plus_14459
-- name    : lean_workbook_plus_14459
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/e062d698-e3e5-4420-aa09-f853e7c02b9a
-- statement:
--   By Cauchy-Schwarz \n $\sum_{cyc}{\frac{a}{2a+b+c}}\sum_{cyc}{\frac{a^2}{2ab+bc+ca}}\geq\frac{(a+b+c)^2}{\sum\limits_{cyc}(2a^2+2ab)}\cdot\frac{(a+b+c)^2}{4(ab+ac+bc)}\geq\frac{9}{16}$ , \n where the last inequality is equivalent to $\sum_{cyc}(2a^4-a^3b-a^3c+3a^2b^2-3a^2bc)\geq0$ , which is obvious.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14459 :
  ∀ a b c : ℝ, (a + b + c) ^ 2 / (2 * a ^ 2 + 2 * b ^ 2 + 2 * c ^ 2 + 2 * a * b + 2 * b * c + 2 * c * a) * (a + b + c) ^ 2 / (4 * a * b + 4 * b * c + 4 * c * a) ≥ 9 / 16   :=  by sorry
