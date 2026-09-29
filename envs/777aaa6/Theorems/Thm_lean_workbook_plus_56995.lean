-- Prove2me | Theorems.Thm_lean_workbook_plus_56995
-- name    : lean_workbook_plus_56995
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/0e716ba7-41b8-45cb-9fe1-7f2171e0a498
-- statement:
--   The sum $ 1 + 2 + ... + 2009$ equals: \n\n $ (A)$ $ 2019045$ \n $ (B)$ $ 2018045$ \n $ (C)$ $ 2009045$ \n $ (D)$ $ 1019045$ \n $ (E)$ $ 2019005$ \n\nthe form ia Arithmetic Progression \n( 1 ,2 , 3 , ........, 2009) \nnumber of terms n is 2009 \na = 1 , r = 1 \nS = (n/2) . (2a + r(n-1)) \n\n= (2009/2) .(2 +2008) \n\n= (2009 . 2010)/2 \n\n=2019045
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56995 ∑ k in Finset.range 2009, k = 2019045   :=  by sorry
