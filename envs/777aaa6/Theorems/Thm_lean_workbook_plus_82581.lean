-- Prove2me | Theorems.Thm_lean_workbook_plus_82581
-- name    : lean_workbook_plus_82581
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/84db27d6-a89c-40dc-8db7-974dfce09445
-- statement:
--   If $x\in \Bbb{Z}$, then it's obvious that $\lfloor x\rfloor=x$ and $\lfloor -x\rfloor=-x$. So $\lfloor x\rfloor+\lfloor-x\rfloor=x+(-x)=0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_82581  (x : ℤ) :
  Int.floor x + Int.floor (-x) = 0   :=  by sorry
