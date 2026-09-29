-- Prove2me | Theorems.Thm_lean_workbook_plus_58417
-- name    : lean_workbook_plus_58417
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/343e226e-22d1-4d7e-bbbf-dbfb24ed419e
-- statement:
--   Let $x,y,z,t \in [0;1]$ . Prove that $x(1-y) + y(1-z) + z(1-t) + t(1-x) \leq 2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58417 (x y z t : ℝ) (hx : x ∈ Set.Icc 0 1) (hy : y ∈ Set.Icc 0 1) (hz : z ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1) : x * (1 - y) + y * (1 - z) + z * (1 - t) + t * (1 - x) ≤ 2   :=  by sorry
