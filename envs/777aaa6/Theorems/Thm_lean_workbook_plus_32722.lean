-- Prove2me | Theorems.Thm_lean_workbook_plus_32722
-- name    : lean_workbook_plus_32722
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/9393838f-a921-42f0-ac71-9761b492534d
-- statement:
--   Since $S(n)$ is defined in this problem as $\frac{n(n+1)}{2}$ , what we're looking for is essentially \n\n $\sum_{n=1}^{100}\frac{n(n+1)}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32722 :
  ∑ n in (Finset.Icc 1 100), (n * (n + 1)) / 2 = 171700   :=  by sorry
