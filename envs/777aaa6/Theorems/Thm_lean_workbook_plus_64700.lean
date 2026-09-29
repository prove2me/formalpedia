-- Prove2me | Theorems.Thm_lean_workbook_plus_64700
-- name    : lean_workbook_plus_64700
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/957ba851-b7cb-4c94-9a77-7d1de88ffae4
-- statement:
--   Prove the lemma: If $x,y,z \in \mathbb{R}$ such that $x+y+z>0, xy+xz+yz>0, xyz>0$, then $x,y,z>0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64700 (x y z : ℝ) (hx : x + y + z > 0) (hy : x*y + x*z + y*z > 0) (hz : x*y*z > 0) : x > 0 ∧ y > 0 ∧ z > 0   :=  by sorry
