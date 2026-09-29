-- Prove2me | Theorems.Thm_lean_workbook_plus_12052
-- name    : lean_workbook_plus_12052
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/d5bac5d1-5815-4324-b72d-cd837176157c
-- statement:
--   Let $a,b,c,d,x,y,z$ be positive reals with $a^2+b^2+c^2 = d^2$ . Show that $x^2+y^2+z^2 \ge \left( \dfrac{ ax+by+cz}{d} \right)^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12052 (a b c d x y z : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (habc : a * a + b * b + c * c = d * d) : x * x + y * y + z * z ≥ (a * x + b * y + c * z) ^ 2 / d ^ 2   :=  by sorry
