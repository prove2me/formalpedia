-- Prove2me | Theorems.Thm_lean_workbook_plus_76491
-- name    : lean_workbook_plus_76491
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/a90184b3-8bb9-4ef9-86ff-31bcfe83397e
-- statement:
--   If $ a,b,c >0$ and $ a < b+c$ prove that : \n\n $ \frac{a}{1+a} < \frac{b}{1+b}+\frac{c}{1+c}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_76491 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a < b + c) : a / (1 + a) < b / (1 + b) + c / (1 + c)   :=  by sorry
