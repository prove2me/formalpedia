-- Prove2me | Theorems.Thm_lean_workbook_plus_69642
-- name    : lean_workbook_plus_69642
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/5ab3731f-26c3-422e-9aea-8a478359481c
-- statement:
--   Let $x, y, z$ are real numbers such that $0 <x, y, z <1$ and $xyz = \left (1-x \right) \left (1-y \right) \left (1-z \right) .$ Show that at least one of the numbers $\left (1-x \right) y, \left (1-y \right) z, \left (1-z \right) x $ is greater than or equal to $\dfrac {1} {4}.$ (JBMO 2009 Shortlist A4)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_69642 (x y z : ℝ) (hx : 0 < x ∧ x < 1) (hy : 0 < y ∧ y < 1) (hz : 0 < z ∧ z < 1) (h : x * y * z = (1 - x) * (1 - y) * (1 - z)) : 1 / 4 ≤ (1 - x) * y ∨ (1 - y) * z ≥ 1 / 4 ∨ (1 - z) * x ≥ 1 / 4   :=  by sorry
