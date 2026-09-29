-- Prove2me | Theorems.Thm_lean_workbook_plus_59597
-- name    : lean_workbook_plus_59597
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/3d048bc3-5cef-4cdc-8c46-5c8b745eff64
-- statement:
--   We have sure $a\ge 2,b\ge 3,c\ge 4$ , thus $\left( 1+\frac{1}{a} \right)\left( 2+\frac{1}{b} \right)\left( 3+\frac{1}{c} \right)\le \left( 1+\frac{1}{2} \right)\left( 2+\frac{1}{3} \right)\left( 3+\frac{1}{4} \right)=\frac{91}{8}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59597 (a b c : ℝ) (ha : 2 ≤ a) (hb : 3 ≤ b) (hc : 4 ≤ c) : (1 + 1 / a) * (2 + 1 / b) * (3 + 1 / c) ≤ 91 / 8   :=  by sorry
