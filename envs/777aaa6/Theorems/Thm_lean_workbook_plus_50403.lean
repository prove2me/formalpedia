-- Prove2me | Theorems.Thm_lean_workbook_plus_50403
-- name    : lean_workbook_plus_50403
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/c14943f2-09f9-4884-ad2b-60497bb87c0d
-- statement:
--   If $a,b,c>0$ , prove that $\sum_{a,b,c} \frac {2}{a+b} \geq \frac {9}{a+b+c}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50403 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 2 / (a + b) + 2 / (b + c) + 2 / (c + a) ≥ 9 / (a + b + c)   :=  by sorry
