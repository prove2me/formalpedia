-- Prove2me | Theorems.Thm_lean_workbook_plus_17116
-- name    : lean_workbook_plus_17116
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/f543afef-c88e-48db-890e-9af27fb5fbd8
-- statement:
--   By Holder: \n $\left(\sum_{cyc}\frac{1}{\sqrt{a^2-ab+b^2}}\right)^2\sum_{cyc}(a^2-ab+b^2)\geq27.$ \n Thus, it remains to prove that: \n $27\geq\frac{9(a+b+c)}{a^3+b^3+c^3}\cdot\sum_{cyc}(2a^2-ab)$ , which is Schur.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17116 :
  ∀ a b c : ℝ, (1 / Real.sqrt (a ^ 2 - a * b + b ^ 2) + 1 / Real.sqrt (b ^ 2 - b * c + c ^ 2) + 1 / Real.sqrt (c ^ 2 - c * a + a ^ 2)) ^ 2 * (a ^ 2 - a * b + b ^ 2 + b ^ 2 - b * c + c ^ 2 + c ^ 2 - c * a + a ^ 2) ≥ 27   :=  by sorry
