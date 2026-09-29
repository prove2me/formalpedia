-- Prove2me | Theorems.Thm_lean_workbook_plus_15936
-- name    : lean_workbook_plus_15936
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/6c9cdd6a-c67e-4836-9f89-b95abb42b200
-- statement:
--   We have \n $LHS-RHS=\frac{1}{4}\sum{a^2(2ab-ac-b^2)^2}+\frac{1}{4}\sum{(b^2+9c^2)(ab-2ac+c^2)^2}+\frac{1}{4}\sum{a^2(a^2-3bc+2c^2)^2}$ \n $(a-b)^2(a-c)^2(b-c)^2+\frac{3}{2}(a+b+c)^2(a^2-ab-ac+b^2-bc+c^2)^2\ge{0}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15936 {a b c : ℝ} :
  (a - b) ^ 2 * (a - c) ^ 2 * (b - c) ^ 2 + (3 / 2) * (a + b + c) ^ 2 * (a ^ 2 - a * b - a * c + b ^ 2 - b * c + c ^ 2) ^ 2 ≥ 0   :=  by sorry
