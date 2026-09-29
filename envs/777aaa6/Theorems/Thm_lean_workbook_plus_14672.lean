-- Prove2me | Theorems.Thm_lean_workbook_plus_14672
-- name    : lean_workbook_plus_14672
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/0cc796f2-9bd8-4f01-8429-2be7b4996de0
-- statement:
--   For $a,b,c,d$ are non-negative real numbers satisfied: $a^3+b^3+c^3+d^3=1$ . Prove that: $\frac{a^2}{1+bcd}+\frac{b^2}{1+cda}+\frac{c^2}{1+dab}+\frac{d^2}{1+abc}\ge 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14672 (a b c d : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hd : d ≥ 0) (habc : a * b * c = 1) : a^3 + b^3 + c^3 + d^3 = 1 → a^2 / (1 + b * c * d) + b^2 / (1 + c * d * a) + c^2 / (1 + d * a * b) + d^2 / (1 + a * b * c) ≥ 1   :=  by sorry
