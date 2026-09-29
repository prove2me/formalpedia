-- Prove2me | Theorems.Thm_lean_workbook_plus_246
-- name    : lean_workbook_plus_246
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/0e92b179-2070-472c-a0e4-22030b4535eb
-- statement:
--   The equation $x+y+z+w = 222$ can be transform into (1) by setting $x_{1}= x-1$ , $x_{2}= y-1$ , $x_{3}= z-1$ and $x_{4}= w-1$ . Making these substitutions, the result is the Diophantine equation $\sum_{i=1}^{4}\: x_{i}\;=\; 218$ . Hence the number of solutions is $A(4,218) = C(4+218-1,218) = C(221,218) = \frac{221 \cdot 220 \cdot 219}{6}= 1774630.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_246 (Nat.choose (4+218-1) 218) = 1774630   :=  by sorry
