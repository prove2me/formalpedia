-- Prove2me | Theorems.Thm_lean_workbook_plus_33791
-- name    : lean_workbook_plus_33791
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/2833346b-c77d-43a0-b5f2-2703c13287e6
-- statement:
--   $\sum_{n=0}^{13} \left\lfloor\frac{10000+2^{n}}{2^{n+1}}\right\rfloor = \sum_{n=0}^{13} \left\lfloor\frac{10000}{2^{n+1}} + \frac{1}{2} \right\rfloor$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_33791 : ∑ n in Finset.range 13, ((10000 + 2^n) / 2^(n+1)) = ∑ n in Finset.range 13, ((10000 / 2^(n+1)) + 1 / 2)   :=  by sorry
