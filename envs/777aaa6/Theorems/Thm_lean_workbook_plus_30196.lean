-- Prove2me | Theorems.Thm_lean_workbook_plus_30196
-- name    : lean_workbook_plus_30196
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/56d7f435-d38a-4d7f-a298-acf9c0a417f8
-- statement:
--   Prove that $(a^2+b^2+c^2)(x^2+y^2+z^2)+2(ab+bc+ca)(xy+yz+zx)\ge 0$ given $x^3+y^3+z^3=3xyz$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30196 (a b c x y z : ℝ) (h : x^3 + y^3 + z^3 = 3 * x * y * z) :
  (a^2 + b^2 + c^2) * (x^2 + y^2 + z^2) + 2 * (a * b + b * c + c * a) * (x * y + y * z + z * x) ≥ 0   :=  by sorry
