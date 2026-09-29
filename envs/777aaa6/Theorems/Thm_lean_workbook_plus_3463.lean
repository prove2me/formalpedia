-- Prove2me | Theorems.Thm_lean_workbook_plus_3463
-- name    : lean_workbook_plus_3463
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/425acca4-1a07-4de6-becc-9c5a313ba500
-- statement:
--   (II)\nSimilar to the solution posted above for (I), we can break this up into two parts, $3^{33}+77\mod4$ and $3^{33}+77\mod25$ .\n\n $3^{33}+77\mod4 \equiv (-1)^{33}+1\mod4 \equiv -1+1\mod4 \equiv 0\mod4$ .\nUsing Euler's Totient Theorem, $3^{20}\equiv 1\mod25$ . It is easy to see that $3^3 \equiv 2\mod25$ as well.\n\nWe can now write the second equation as $(3^{20})(3^{3})^{4}(3^1)+77\mod25 \equiv (1)(2)^4(3) + 77\mod25 \equiv 48+77\mod25 \equiv 125\mod25 \equiv 0\mod25.$\n\nBecause this is congruent to 0 mod 25 and 4, it is congruent to 0 mod 100.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3463 :
  (3^33 + 77) % 100 = 0   :=  by sorry
