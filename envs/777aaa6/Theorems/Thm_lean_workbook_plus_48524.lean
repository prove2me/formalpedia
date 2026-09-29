-- Prove2me | Theorems.Thm_lean_workbook_plus_48524
-- name    : lean_workbook_plus_48524
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/89f8ad72-6564-40f7-bf65-52b1533c4b16
-- statement:
--   Find the value of $mnp$ where $m = ab+cd$, $n = ac+bd$, and $p = ad+bc$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_48524 (a b c d m n p : ℤ) (hm : m = a*b + c*d) (hn : n = a*c + b*d) (hp : p = a*d + b*c) : m*n*p = (a*b + c*d)*(a*c + b*d)*(a*d + b*c)   :=  by sorry
