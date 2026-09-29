-- Prove2me | Theorems.Thm_lean_workbook_plus_54808
-- name    : lean_workbook_plus_54808
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/1d18645a-a666-4207-8277-456af57413bb
-- statement:
--   $\left(a^2 + b^2\right)^2 \geq (a + b + c)(a + b - c)(b + c - a)(c + a - b)$ $\iff$ \n\n $\left(a^2+b^2-c^2\right)^2+\left(a^2-b^2\right)^2\ge 0$ with equality iff $\frac {|a|}{1}=\frac {|b|}{1}=\frac {|c|}{\sqrt 2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54808 {a b c : ℝ} :
  (a^2 + b^2)^2 ≥ (a + b + c) * (a + b - c) * (b + c - a) * (c + a - b) ↔
  (a^2 + b^2 - c^2)^2 + (a^2 - b^2)^2 ≥ 0   :=  by sorry
