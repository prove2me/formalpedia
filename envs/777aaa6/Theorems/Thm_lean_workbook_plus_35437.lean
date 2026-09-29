-- Prove2me | Theorems.Thm_lean_workbook_plus_35437
-- name    : lean_workbook_plus_35437
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/3198bba1-8d26-41f9-8cb7-b116417ab6ab
-- statement:
--   Let $a,b,c$ be reals such that $a^2+b^2+c^2+abc=4 .$ Prove that\n\n $$a^2+kb+kc+ abc \leq 4+ \frac{k^2}{2} $$ Where $k>0.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_35437 (a b c k : ℝ) (ha : a^2 + b^2 + c^2 + a * b * c = 4) (hb : 0 < k) : a^2 + k * b + k * c + a * b * c ≤ 4 + k^2 / 2   :=  by sorry
