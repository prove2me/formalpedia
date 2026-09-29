-- Prove2me | Theorems.Thm_lean_workbook_plus_79826
-- name    : lean_workbook_plus_79826
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/8d8b9f44-5cea-4358-ae8e-be1c9cb53f6b
-- statement:
--   Through the partial fraction decomposition, we have: \n\n $ \sum^{1996}_{n = 1} \frac {1}{2n} - \frac {1}{n + 1} + \frac {1}{2(n + 2)}$ \n\n Now, writing the middle term as $ \frac {2}{2(n + 1)}$ and factoring out $ \frac {1}{2}$ : \n\n $ \sum^{1996}_{n = 1} \frac {1}{n} - \frac {1}{n + 1} + \frac {1}{n + 2} - \frac {1}{n + 1}$ \n\n This equals \n\n $ \frac {1}{2} \cdot \sum^{1996}_{n = 1} \left[ \frac{1}{n(n + 1)} - \frac{1}{(n + 1)(n + 2)} \right]$ \n\n It is not very hard to see how this sequence telescopes. The inside is left with $ \frac {1}{1 \cdot 2} - \frac {1}{1997 \cdot 1998}$ . Multiply that by 1/2 to get the final answer ---- E.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79826 :
  ∑ k in (Finset.Icc 1 1996), (1 / (2 * k) - 1 / (k + 1) + 1 / (2 * (k + 2))) = 1 / 2   :=  by sorry
