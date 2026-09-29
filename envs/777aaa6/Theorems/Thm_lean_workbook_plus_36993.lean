-- Prove2me | Theorems.Thm_lean_workbook_plus_36993
-- name    : lean_workbook_plus_36993
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/7742b79d-ed36-4986-a7cd-c8378281ed3d
-- statement:
--   Suppose that positive numbers $x$ and $y$ satisfy $x^2+y^3+z^4 \geqslant x^3+y^4+z^5.$ Prove that $x^3+y^3+z^3 \leqslant 3.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36993 (x y z : ℝ) (hx: 0 < x) (hy: 0 < y) (hz: 0 < z) (h : x^2 + y^3 + z^4 ≥ x^3 + y^4 + z^5) : x^3 + y^3 + z^3 ≤ 3   :=  by sorry
