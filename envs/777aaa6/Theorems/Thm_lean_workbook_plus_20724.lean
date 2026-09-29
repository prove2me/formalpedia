-- Prove2me | Theorems.Thm_lean_workbook_plus_20724
-- name    : lean_workbook_plus_20724
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/b36c8843-bd3d-474c-bc26-845a4551a4d8
-- statement:
--   Let $f(x)=x-ln(1+x)$\n\nSo $f'(x)=1-\frac{1}{1+x}$\n\nwhen $-1<x<0$ , $f'(x)<0$ ; when $x>0$ , $f'(x)>0$\n\nmeans that $f(x)>=f(0)=0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20724 (x : ℝ) (hx : 0 ≤ x) : x - Real.log (1 + x) ≥ 0   :=  by sorry
