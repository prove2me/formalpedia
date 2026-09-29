-- Prove2me | Theorems.Thm_lean_workbook_plus_46161
-- name    : lean_workbook_plus_46161
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/028e2856-0ab0-4238-bd42-83665914fdd3
-- statement:
--   Using the formula for the sum of an arithmetico-geometric sequence, we find that: \n \begin{align*} 123456789 &= \dfrac{9 + \dfrac{-1 \cdot 10 \cdot (1-10^9)}{1-10} - (9+9 \cdot (-1)) \cdot 10^9}{1 - 10} \ &= \dfrac{9 + \dfrac{10 \cdot (1 - 10^9)}{9}}{-9} \ &= -1 + \dfrac{-10 \cdot (1-10^9)}{81} \ &= \dfrac{10^{10} - 91}{81} \end{align*} \n Similarly, we can find that \n $987654321 = \dfrac{8 \cdot 10^{10} + 1}{81}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46161 :
  123456789 = (10^10 - 91) / 81   :=  by sorry
