-- Prove2me | Theorems.Thm_lean_workbook_plus_14050
-- name    : lean_workbook_plus_14050
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/97027c48-80a5-475b-89c4-a07ff62897f6
-- statement:
--   Let's calculate this using Abel Formula. \n\nFor the top, say $x_i = 101-i$ for $i = 1,2, \dots ,100$ and $y_i = 5^{j-1}$ for $j = 1,2, \dots ,100$ . \n\nLet $z_i = \displaystyle\sum\limits_{k=1}^{i} x_i$ , then $100+99\cdot5+98\cdot 5^{2}+.....+5^{99}$ becomes \n\n$$\displaystyle\sum\limits_{i=1}^{99} z_i = \frac{5^{101}-405}{16}$$ .Doing similar things for the denominator part, we get \n\n$$1+2\cdot 5+3\cdot 5^{2}+......+100\cdot 5^{99} = \frac{399 \cdot 5^{100} + 1}{16}$$ \n\nDividing these, we get the desired result.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14050 :
  (∑ k in (Finset.Icc 1 100), (101 - k) * 5^k) / (∑ k in (Finset.Icc 1 100), k * 5^k) =
  (5^101 - 405) / 16   :=  by sorry
