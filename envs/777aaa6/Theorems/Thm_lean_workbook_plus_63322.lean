-- Prove2me | Theorems.Thm_lean_workbook_plus_63322
-- name    : lean_workbook_plus_63322
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/f531d021-f5ab-4660-ac99-db0d224ff5f9
-- statement:
--   The sum $ 1+2+...+2009$ equals: \n\n $ (A)$ $ 2019045$ \n $ (B)$ $ 2018045$ \n $ (C)$ $ 2009045$ \n $ (D)$ $ 1019045$ \n $ (E)$ $ 2019005$ \n\nThe formula for the sum of the first $ n$ number is $ \frac{n(n+1)}{2}$ \n\nPlugging in, $ S=\frac{2009 \cdot 2010}{2}=2009 \cdot 1005=2009000+10045=2019045$ so A
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63322 :
  ∑ k in Finset.range 2009, k = 2019045   :=  by sorry
