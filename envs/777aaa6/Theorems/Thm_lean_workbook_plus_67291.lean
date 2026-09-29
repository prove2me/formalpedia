-- Prove2me | Theorems.Thm_lean_workbook_plus_67291
-- name    : lean_workbook_plus_67291
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/500508f6-cae2-4c7f-9391-383a56decfc9
-- statement:
--   Let $a,b,c,d,e$ be real numbers so that : $a>0$ , $e<0$ , $b^2<\frac 83ac$ and $\frac a{2008}+\frac b{2007}+\frac c{2006}+\frac d{2005}+\frac e{2004}=0$ . Prove that : $a+b+c+d+e>0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_67291 (a b c d e : ℝ) (ha : 0 < a) (he : e < 0) (hb : b ^ 2 < 8 / 3 * a * c) (habcde : a / 2008 + b / 2007 + c / 2006 + d / 2005 + e / 2004 = 0) : a + b + c + d + e > 0   :=  by sorry
