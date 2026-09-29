-- Prove2me | Theorems.Thm_lean_workbook_plus_79483
-- name    : lean_workbook_plus_79483
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/4a7c7c48-3d1b-4496-adfc-a9d355e642c8
-- statement:
--   Min: Suppose that: $x\ge y\ge z \Rightarrow 3x^4\ge x^4+y^4+z^4=1 \Rightarrow x^2\ge \frac{\sqrt{3}}{3}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79483 :  ∀ x y z : ℝ, x ≥ y ∧ y ≥ z ∧ 3 * x ^ 4 ≥ x ^ 4 + y ^ 4 + z ^ 4 ∧ x ^ 4 + y ^ 4 + z ^ 4 = 1 → x ^ 2 ≥ Real.sqrt 3 / 3   :=  by sorry
