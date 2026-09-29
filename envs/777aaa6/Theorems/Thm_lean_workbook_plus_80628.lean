-- Prove2me | Theorems.Thm_lean_workbook_plus_80628
-- name    : lean_workbook_plus_80628
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/323ce85d-c972-4017-bf95-405e1f638d62
-- statement:
--   Show that if $a,b,x$ and $y$ are real numbers such that $a>b>0$ and $x>y>0$ then $\frac{a+y}{b+y}>\frac{a+x}{b+x}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80628 (a b x y : ℝ) (hab : a > b ∧ b > 0) (hxy : x > y ∧ y > 0) :
  (a + y) / (b + y) > (a + x) / (b + x)   :=  by sorry
