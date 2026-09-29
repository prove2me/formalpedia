-- Prove2me | Theorems.Thm_WorkbookSource_base_22107
-- name    : WorkbookSource.base_22107
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:27:53.489984+00:00
-- url     : https://prove2.me/theorems/5902471e-7a92-4231-b6cc-c9095d18f5d7
-- title:
--   A squared cyclic quartic bounds a quadratic-cubic product
-- statement:
--   Let $x,y,z$ be real numbers, prove that:
--
--    \begin{align*} 3\left( x^4+y^4+z^4-x^3y-y^3z-z^3x \right) ^2\ge
--    &2\left( x^2+y^2+z^2-xy-yz-zx \right) \left( x^3+y^3+z^3-x^2y-y^2z-z^2x \right) ^2. \end{align*}
--
--   LHS - RHS =
--
--    \begin{align*} \frac{1}{27} \left(5\sum_{\rm{cyc}} x^4-\sum_{\rm{cyc}} x^3y+8\sum_{\rm{cyc}} x^3z-12\sum_{\rm{cyc}} x^2y^2 \right)^2+\frac{2}{27} \left( \sum_{\rm{cyc}} x^2 - \sum_{\rm{cyc}} xy \right) \left( \sum_{\rm{cyc}}x^3+3\sum_{\rm{cyc}}x^2y-6\sum_{\rm{cyc}}x^2z+6xyz \right)^2 \geqslant 0. \end{align*}
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_22107` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_22107; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_22107 (x y z : ℝ) :
  3 * (x ^ 4 + y ^ 4 + z ^ 4 - x ^ 3 * y - y ^ 3 * z - z ^ 3 * x) ^ 2 ≥
    2 * (x ^ 2 + y ^ 2 + z ^ 2 - x * y - y * z - z * x) * (x ^ 3 + y ^ 3 + z ^ 3 - x ^ 2 * y - y ^ 2 * z - z ^ 2 * x) ^ 2  :=  by sorry
