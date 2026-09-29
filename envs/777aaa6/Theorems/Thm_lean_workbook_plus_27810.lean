-- Prove2me | Theorems.Thm_lean_workbook_plus_27810
-- name    : lean_workbook_plus_27810
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/21bdcf97-fb1f-43f6-be9e-b01da3020ec8
-- statement:
--   $4\, \left( a-c \right) ^{2} \left( c+a \right) ^{2}+4\, \left( b-d \right) ^{2} \left( b+d \right) ^{2}= \left( {b}^{2}-{d}^{2}-{a}^{2}+{c}^{2} \right) ^{2}+ \left( {c}^{2}-{a}^{2}-{b}^{2}+{d}^{2} \right) ^{2}+ \left( {a}^{2}-{b}^{2}-{c}^{2}+{d}^{2} \right) ^{2}+ \left( {a}^{2}-{c}^{2}-{d}^{2}+{b}^{2} \right) ^{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27810 :
  ∀ a b c d : ℝ,
    4 * (a - c)^2 * (c + a)^2 + 4 * (b - d)^2 * (b + d)^2 =
    (b^2 - d^2 - a^2 + c^2)^2 + (c^2 - a^2 - b^2 + d^2)^2 +
    (a^2 - b^2 - c^2 + d^2)^2 + (a^2 - c^2 - d^2 + b^2)^2   :=  by sorry
