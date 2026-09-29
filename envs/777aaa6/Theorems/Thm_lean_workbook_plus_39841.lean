-- Prove2me | Theorems.Thm_lean_workbook_plus_39841
-- name    : lean_workbook_plus_39841
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/beb47a6e-7f4c-4801-9ecf-45cd1528698a
-- statement:
--   If the mean of $a$ and $b$ is $5$ , then $a+b=5\cdot2=10$ . Do this for the others and get $b+c=14$ and $a+c=24$ . Adding these three equations up, we get $2a+2b+2c=48$ . Dividing both sides by $2$ , we get $\boxed{a+b+c=24}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39841  (a b c : ℝ)
  (h₀ : (a + b) / 2 = 5)
  (h₁ : (b + c) / 2 = 7)
  (h₂ : (c + a) / 2 = 12) :
  a + b + c = 24   :=  by sorry
