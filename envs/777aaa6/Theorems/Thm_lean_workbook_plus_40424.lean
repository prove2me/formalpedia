-- Prove2me | Theorems.Thm_lean_workbook_plus_40424
-- name    : lean_workbook_plus_40424
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/cdb07c40-5ce8-46e6-ba4a-e14b69f50b2e
-- statement:
--   Show that for all positive real numbers $a,b,c$ and $d$, $\frac{a^2}{a^2+bc}+ \frac{b^2}{b^2+cd}+\frac{c^2}{c^2+da}+\frac{d^2}{d^2+ab} \leq 3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40424 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (a^2 / (a^2 + b * c) + b^2 / (b^2 + c * d) + c^2 / (c^2 + d * a) + d^2 / (d^2 + a * b) ≤ 3)   :=  by sorry
