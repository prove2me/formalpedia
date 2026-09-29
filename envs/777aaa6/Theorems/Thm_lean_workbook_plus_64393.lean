-- Prove2me | Theorems.Thm_lean_workbook_plus_64393
-- name    : lean_workbook_plus_64393
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/f4cde3e2-93b3-4e7e-83cf-dfcd95208352
-- statement:
--   If $a,b,c$ are real numbers such that $a+b+c=0$ , then prove that \n $ \cfrac{a^5+b^5+c^5}{5}=\left(\cfrac{a^3+b^3+c^3}{3}\right)\left(\cfrac{a^2+b^2+c^2}{2}\right) $ \nThis is Problem 33 on pg. 532 of Pre-College Math. \n\nRather if there is any elegant way and some clever trick that may be applied is preferable, for even I have a solution by just substituting for $c$ as $-a-b$ and then expanding everything on the LHS and RHS.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64393 (a b c : ℝ) (h : a + b + c = 0) : (a^5 + b^5 + c^5) / 5 = (a^3 + b^3 + c^3) / 3 * (a^2 + b^2 + c^2) / 2   :=  by sorry
