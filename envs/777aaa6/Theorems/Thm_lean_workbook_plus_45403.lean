-- Prove2me | Theorems.Thm_lean_workbook_plus_45403
-- name    : lean_workbook_plus_45403
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/a64a172a-fbd8-4d28-8a61-d1480288eec3
-- statement:
--   prove that \n ${\frac {a}{b}}+{\frac {b}{c}}+{\frac {c}{d}}+{\frac {d}{a}}+{\frac {253}{10}}\,{\frac {ab+bc+cd+ad+ac+bd}{ \left( a+b+c+d \right) ^{2}}}\geq {\frac {1079}{80}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_45403 : ∀ a b c d : ℝ, (a / b + b / c + c / d + d / a + 253 / 10 * (a * b + b * c + c * d + d * a + a * c + b * d) / (a + b + c + d) ^ 2) ≥ 1079 / 80   :=  by sorry
