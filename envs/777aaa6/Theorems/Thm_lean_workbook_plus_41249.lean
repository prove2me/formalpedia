-- Prove2me | Theorems.Thm_lean_workbook_plus_41249
-- name    : lean_workbook_plus_41249
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/c73898f0-5c48-486d-a648-f31ec10bfa5f
-- statement:
--   Either, note that\n$\left(a^4+b^4+c^4\right)+3\left(b^2c^2+c^2a^2+a^2b^2\right)$\n$-2\left(bc\left(b^2+c^2\right)+ca\left(c^2+a^2\right)+ab\left(a^2+b^2\right)\right)$\n$=\left(\frac{b^4+c^4}{2}+3b^2c^2-2bc\left(b^2+c^2\right)\right)+\left(\frac{c^4+a^4}{2}+3c^2a^2-2ca\left(c^2+a^2\right)\right)$\n$+\left(\frac{a^4+b^4}{2}+3a^2b^2-2ab\left(a^2+b^2\right)\right)$\n$=\frac{\left(b-c\right)^4}{2}+\frac{\left(c-a\right)^4}{2}+\frac{\left(a-b\right)^4}{2}\geq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_41249 {a b c : ℝ} :
  a^4 + b^4 + c^4 + 3 * (b^2 * c^2 + c^2 * a^2 + a^2 * b^2) -
    2 * (b * c * (b^2 + c^2) + c * a * (c^2 + a^2) + a * b * (a^2 + b^2)) ≥ 0   :=  by sorry
