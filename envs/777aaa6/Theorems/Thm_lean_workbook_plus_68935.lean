-- Prove2me | Theorems.Thm_lean_workbook_plus_68935
-- name    : lean_workbook_plus_68935
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/20c3542c-3d3f-4905-827d-b3954fe9f616
-- statement:
--   Indeed. Solution using sigma/sum notation\nWe have $ 1 \cdot 2 + 2 \cdot 3 + \ldots + 99 \cdot 100 = $\n$$ \sum_{k = 1}^{99} k \cdot (k + 1) = \sum_{k = 1}^{99} k^2 + k = $\n$$ \sum_{k = 1}^{99} k^2 + \sum_{k = 1}^{99} k $$ By the sums of integers and squares formulae, we have\n$$ \sum_{k = 1}^{99} k^2 = \frac{99 \cdot 100 \cdot 199}{6} $$\n$$ \sum_{k = 1}^{99} k = \frac{99 \cdot 100}{2} = \frac{99 \cdot 100 \cdot 3}{6} $$Therefore, the desired sum is $ \frac{99 \cdot 100 \cdot 202}{6} = 33 \cdot 100 \cdot 101 = \boxed{333300} $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_68935 :
  ∑ k in (Finset.Icc 1 99), (k * (k + 1)) = 333300   :=  by sorry
