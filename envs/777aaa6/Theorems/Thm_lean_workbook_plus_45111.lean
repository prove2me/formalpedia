-- Prove2me | Theorems.Thm_lean_workbook_plus_45111
-- name    : lean_workbook_plus_45111
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/269f0419-f08c-476c-9ae9-7b05b84e0dba
-- statement:
--   Let $a,b,c $ be positive real numbers . \n $a^3+b^3+c^3-3abc\ge2 \left(\dfrac{b+c}{2}-a\right)^3.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_45111 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^3 + b^3 + c^3 - 3 * a * b * c ≥ 2 * ((b + c) / 2 - a)^3   :=  by sorry
