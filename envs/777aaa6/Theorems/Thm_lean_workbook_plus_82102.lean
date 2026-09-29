-- Prove2me | Theorems.Thm_lean_workbook_plus_82102
-- name    : lean_workbook_plus_82102
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/e1e51388-c40c-48db-8440-4cad4817d53b
-- statement:
--   If $ x,y,z>0$ and $ x+y+z=4$ , what is the maximum value of $ xy+yz+xz$ ?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_82102 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x + y + z = 4) : (x * y + y * z + z * x) ≤ 16/3 ∧ (∃ x y z : ℝ, (x * y + y * z + z * x) = 16/3)   :=  by sorry
