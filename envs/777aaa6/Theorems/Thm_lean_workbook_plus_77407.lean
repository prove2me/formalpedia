-- Prove2me | Theorems.Thm_lean_workbook_plus_77407
-- name    : lean_workbook_plus_77407
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/ddb28761-7434-46f0-bfdb-df6f89472204
-- statement:
--   Prove that if $a+b+c=0$, then $\frac{a^2+b^2+c^2}{2}.\frac{a^3+b^3+c^3}{3}=\frac{a^5+b^5+c^5}{5}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77407 (a b c : ℝ) : a + b + c = 0 → (a ^ 2 + b ^ 2 + c ^ 2) / 2 * (a ^ 3 + b ^ 3 + c ^ 3) / 3 = (a ^ 5 + b ^ 5 + c ^ 5) / 5   :=  by sorry
