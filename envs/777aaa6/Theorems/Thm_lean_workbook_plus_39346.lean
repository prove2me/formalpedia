-- Prove2me | Theorems.Thm_lean_workbook_plus_39346
-- name    : lean_workbook_plus_39346
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/68e3578e-2045-4b2d-8225-d642b8ae9fba
-- statement:
--   $ \left( {a}^{4}+{b}^{4}+{c}^{4} \right) \left( bc+ac+ab \right) - \left( {a}^{2}{b}^{2}+{b}^{2}{c}^{2}+{a}^{2}{c}^{2} \right) \left( { b}^{2}+{c}^{2}+{a}^{2} \right) $ \n $ = \left( a-b \right) ^{2} \left( a{b}^{3}+{a}^{2}{b}^{2}+{a}^{3}b+3/4\,b{c}^{2}a \right) + \left( b-c \right) ^{2} \left( b{c}^{3}+{b}^{2}{c}^{2}+{b}^{3}c+3/4\,c{a}^{2}b \right) + \left( c-a \right) ^{2} \left( c{a}^{3}+{a}^{2}{c}^{2}+{c}^{3}a+3/4\,a{b}^{2}c \right)$ \n $ +1/4\, \left( 2\,a-b-c \right) ^{2}c{a}^{2b}+1/4\, \left( 2\,b-a-c \right) ^{2}a{b}^{2}c+1/4\, \left( 2\,c-a-b \right) ^{2}b{c}^{2}a$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39346 b c : ℝ) :
  (a^4 + b^4 + c^4) * (b * c + a * c + a * b) - (a^2 * b^2 + b^2 * c^2 + a^2 * c^2) * (b^2 + c^2 + a^2) =
  (a - b)^2 * (a * b^3 + a^2 * b^2 + a^3 * b + (3 / 4) * b * c^2 * a) +
  (b - c)^2 * (b * c^3 + b^2 * c^2 + b^3 * c + (3 / 4) * c * a^2 * b) +
  (c - a)^2 * (c * a^3 + a^2 * c^2 + c^3 * a + (3 / 4) * a * b^2 * c) +
  (1 / 4) * (2 * a - b - c)^2 * c * a^2 * b +
  (1 / 4) * (2 * b - a - c)^2 * a * b^2 * c +
  (1 / 4) * (2 * c - a - b)^2 * b * c^2 * a   :=  by sorry
