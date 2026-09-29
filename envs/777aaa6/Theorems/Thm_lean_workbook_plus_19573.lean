-- Prove2me | Theorems.Thm_lean_workbook_plus_19573
-- name    : lean_workbook_plus_19573
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/ccd55489-f227-4cff-802e-a1b886dcc427
-- statement:
--   There are $ 10^{5}$ total ways. \n\nThere are $ \binom{5}{3}= 10 \textrm{ triplets}$ . \n\nPick one of these triplets. There are $ 10$ ways to choose the numbers inside the triplet, and $ 9^{2}= 81$ ways to choose the numbers outside the triplet. \n\nThus, the number of desired outcomes is: \n\n $ 10 \cdot 10 \cdot 9^{2}$ \n\nThe total is $ 10^{5}$ ; hence, our probability is: \n\n $ \frac{10^{2}\cdot 9^{2}}{10^{5}}= \boxed{\frac{81}{1000}}$ \n\nEDIT: Fixed $ \text{\LaTeX}$ error.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19573 :
  ((10^2 * 9^2)/10^5 : ℚ) = 81/1000   :=  by sorry
