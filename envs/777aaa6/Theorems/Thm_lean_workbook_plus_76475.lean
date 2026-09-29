-- Prove2me | Theorems.Thm_lean_workbook_plus_76475
-- name    : lean_workbook_plus_76475
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/1432579f-8754-446a-950f-a898a560e3ef
-- statement:
--   Prove $(x^2+y^2)(z^2+t^2)=(xz+yt)^2+(xt-yz)^2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_76475 (x y z t : ℝ) : (x^2+y^2)*(z^2+t^2) = (x*z+y*t)^2+(x*t-y*z)^2   :=  by sorry
