-- Prove2me | Theorems.Thm_lean_workbook_plus_82047
-- name    : lean_workbook_plus_82047
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/7a1776d2-ec78-47f6-ad13-78423e988367
-- statement:
--   Given $a^x = a^y$ for real numbers $a>1$, $x$, and $y$, show that $x=y$ using the definition of the logarithm and the fact that $x=$ sup $S$, where $S$ is the set of all real $n$ satisfying $a^n<m$, is a solution to $a^x=m$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_82047 (a x y : ℝ) (ha : 1 < a) : a^x = a^y → x = y   :=  by sorry
