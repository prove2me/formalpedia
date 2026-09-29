-- Prove2me | Theorems.Thm_lean_workbook_plus_45783
-- name    : lean_workbook_plus_45783
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/cf1335df-7202-4673-b92d-2151409bf40b
-- statement:
--   Solution 19Note that $11$ works for any number, $13,~17$ work for multiples of $4$ , $19$ works for multiples of $2$ , and $15$ never works. Thus our answer is $\dfrac{1}{5}\left(\dfrac{20+2\cdot 5+10+0}{20}\right)=\boxed{\text{(E)}~\dfrac{2}{5}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_45783 :
  (1 / 5) * ((20 + 2 * 5 + 10 + 0) / 20) = 2 / 5   :=  by sorry
