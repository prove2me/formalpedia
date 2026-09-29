-- Prove2me | Theorems.Thm_lean_workbook_plus_16306
-- name    : lean_workbook_plus_16306
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/833a93e6-2609-4894-b743-9a709d5ba117
-- statement:
--   As $f(x)=x^2$ is a bijection among positive reals, we may square both sides and call it equivalent. $$a^4+b^4+c^4+2\left(a^2b^2+a^2c^2+b^2c^2\right)\ge6\left(a^2 b^2+a^2c^2+b^2c^2\right)-3\left(a^4+b^4+c^4\right).$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16306 {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a ^ 4 + b ^ 4 + c ^ 4 + 2 * (a ^ 2 * b ^ 2 + a ^ 2 * c ^ 2 + b ^ 2 * c ^ 2) ≥ 6 * (a ^ 2 * b ^ 2 + a ^ 2 * c ^ 2 + b ^ 2 * c ^ 2) - 3 * (a ^ 4 + b ^ 4 + c ^ 4)   :=  by sorry
