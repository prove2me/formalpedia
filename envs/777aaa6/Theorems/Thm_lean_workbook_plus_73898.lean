-- Prove2me | Theorems.Thm_lean_workbook_plus_73898
-- name    : lean_workbook_plus_73898
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/9e732abc-a91d-423d-ab82-440cf16f190d
-- statement:
--   Using the identity $$\sin (a) - \sin (b) = 2\cos\left(\frac{a+b}{2}\right)\sin\left(\frac{a-b}{2}\right),$$ we obtain the equation \n $$-2\cos(2\pi x)\sin(\pi x)=0.$$ Solving the equation we have \n $$x=\frac{1}{4}+\frac{k}{2},k$$ for $k \in \mathbb{Z}$ . Hence $$x \in \left\{0, \frac{1}{4}, \frac{3}{4}, 1, \frac{5}{4}, \frac{7}{4}, 2, \frac{9}{4}, \frac{11}{4}, 3 \right\}$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_73898 :
  ∀ x : ℝ, (x ∈ ({0, 1/4, 3/4, 1, 5/4, 7/4, 2, 9/4, 11/4, 3} : Set ℝ) ↔
    sin (2 * π * x) - sin (π * x) = 0)   :=  by sorry
