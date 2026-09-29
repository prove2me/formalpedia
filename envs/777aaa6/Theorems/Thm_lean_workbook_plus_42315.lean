-- Prove2me | Theorems.Thm_lean_workbook_plus_42315
-- name    : lean_workbook_plus_42315
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/668897a4-188d-418d-8e0f-7c40cb919897
-- statement:
--   Let $ f(n)=\lfloor{\frac{n}{1}}\rfloor+\lfloor{\frac{n}{2}}\rfloor+\lfloor{\frac{n}{3}}\rfloor+\lfloor{\frac{n}{4}}\rfloor+\lfloor{\frac{n}{5}}\rfloor+...$ \n\nCompute $ \displaystyle\sum^{10}_{k=1}f(k!)-\displaystyle\sum^{10}_{k=1}f(k!-1)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42315 :
  (∑ k in Finset.Icc 1 10, (∑ n in Finset.Icc 1 k, (n / k))) -
  (∑ k in Finset.Icc 1 10, (∑ n in Finset.Icc 1 (k - 1), (n / (k - 1)))) = 647   :=  by sorry
