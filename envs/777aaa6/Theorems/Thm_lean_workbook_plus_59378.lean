-- Prove2me | Theorems.Thm_lean_workbook_plus_59378
-- name    : lean_workbook_plus_59378
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/34e86f27-b5e5-41a6-9aea-b6b3cd10dd56
-- statement:
--   After homogeneous inequality equivalent to \n $\frac{11+2\sqrt{10}}{81}\sum \left[3a^2+(4-\sqrt{10})b^2+3c^2+(2\sqrt{10}-5)b(c+a)-3\sqrt{10}ca\right]^2 \geqslant 0.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59378 (a b c : ℝ) :
  (11 + 2 * Real.sqrt 10) / 81 * (3 * a ^ 2 + (4 - Real.sqrt 10) * b ^ 2 + 3 * c ^ 2 + (2 * Real.sqrt 10 - 5) * b * (c + a) - 3 * Real.sqrt 10 * c * a) ^ 2 +
    (11 + 2 * Real.sqrt 10) / 81 * (3 * b ^ 2 + (4 - Real.sqrt 10) * c ^ 2 + 3 * a ^ 2 + (2 * Real.sqrt 10 - 5) * c * (a + b) - 3 * Real.sqrt 10 * a * b) ^ 2 +
    (11 + 2 * Real.sqrt 10) / 81 * (3 * c ^ 2 + (4 - Real.sqrt 10) * a ^ 2 + 3 * b ^ 2 + (2 * Real.sqrt 10 - 5) * a * (b + c) - 3 * Real.sqrt 10 * b * c) ^ 2 ≥ 0   :=  by sorry
