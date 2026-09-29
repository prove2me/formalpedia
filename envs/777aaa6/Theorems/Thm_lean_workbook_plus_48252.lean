-- Prove2me | Theorems.Thm_lean_workbook_plus_48252
-- name    : lean_workbook_plus_48252
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/898133dc-f514-437a-8a53-e188d2bbdf53
-- statement:
--   Prove that for positive reals $ a,b,c$ , \n $ \frac {a^2 + ac}{2b + a + c} + \frac {b^2 + ba}{2c + a + b} + \frac {c^2 + cb}{2a + b + c} \ge 2(a + b + c)$ \nwhen does the equality hold?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_48252 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + a*c)/(2*b + a + c) + (b^2 + b*a)/(2*c + a + b) + (c^2 + c*b)/(2*a + b + c) ≥ 2*(a + b + c)   :=  by sorry
