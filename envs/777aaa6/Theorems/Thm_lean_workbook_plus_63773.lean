-- Prove2me | Theorems.Thm_lean_workbook_plus_63773
-- name    : lean_workbook_plus_63773
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/f3e95353-58a8-48c9-a333-337e82dd3b23
-- statement:
--   Show $\forall a,b,c \in \mathbb{R^+}$ we have : \n $a^2(b+c)+b^2(a+c)+c^2(a+b)\geq 6abc$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63773 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^2 * (b + c) + b^2 * (a + c) + c^2 * (a + b) ≥ 6 * a * b * c   :=  by sorry
