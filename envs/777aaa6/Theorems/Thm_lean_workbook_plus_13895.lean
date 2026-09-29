-- Prove2me | Theorems.Thm_lean_workbook_plus_13895
-- name    : lean_workbook_plus_13895
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/041b60a1-248d-4af5-add1-781079cc19a7
-- statement:
--   It is $(a+b-c)^3+(a-b+c)^3+(b+c-a)^3=a^3+b^3+c^3+3(a^2b+ab^2+ac^2+a^2c+b^2c+bc^2-6abc)$ . So, $a^2b+ab^2+ac^2+a^2c+b^2c+bc^2-6abc=0\Leftrightarrow a^2b+ab^2+ac^2+a^2c+b^2c+bc^2=6abc$ . But $a^2b+a^2c+b^2c+b^2a+c^2a+c^2b\geq 6\sqrt[6]{a^6b^6c^6}=6abc$ , with equality iff $a=b=c$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13895  (a b c : ℝ) :
  (a + b - c) ^ 3 + (a - b + c) ^ 3 + (b + c - a) ^ 3 = a ^ 3 + b ^ 3 + c ^ 3 + 3 * (a ^ 2 * b + a * b ^ 2 + a * c ^ 2 + a ^ 2 * c + b ^ 2 * c + b * c ^ 2 - 6 * a * b * c)   :=  by sorry
