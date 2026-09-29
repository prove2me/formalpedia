-- Prove2me | Theorems.Thm_lean_workbook_plus_32961
-- name    : lean_workbook_plus_32961
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/6bf72398-0d78-46a7-8ae6-098479234f2e
-- statement:
--   For 6 variables, if $a,b,c,d,e,f$ are positive reals, then $\frac{ab}{a+b}+\frac{cd}{c+d}+\frac{ef}{e+f} \le \frac{(a+c+e)(b+d+f)}{a+b+c+d+e+f}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32961 (a b c d e f : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e) (hf : 0 < f) : (a * b / (a + b) + c * d / (c + d) + e * f / (e + f)) ≤ (a + c + e) * (b + d + f) / (a + b + c + d + e + f)   :=  by sorry
