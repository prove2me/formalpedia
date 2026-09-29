-- Prove2me | Theorems.Thm_lean_workbook_plus_37727
-- name    : lean_workbook_plus_37727
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/5fe6abf1-edcc-475d-a2e5-fc7e7fe45e49
-- statement:
--   the idea of this problem is that you have to know the properties\n\n$|w*z|=|w|*|z|$ and $\frac{|w|}{|z|}=\left|\frac{w}{z}\right|$ \n\nfor complex numbers $w$ and $z$, with $z\ne 0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37727 (w z : ℂ) (h : z ≠ 0) : ‖w * z‖ = ‖w‖ * ‖z‖   :=  by sorry
