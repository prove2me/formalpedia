-- Prove2me | Theorems.Thm_lean_workbook_plus_45444
-- name    : lean_workbook_plus_45444
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/4c53a605-49f5-41b6-8178-fb73c812077f
-- statement:
--   Prove that if $x,y,z \in \mathbb{R}$ and $x+y+z \ge xyz$ , then $x^2+y^2+z^2 \ge xyz$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_45444 (x y z : ℝ) (h : x + y + z ≥ x * y * z) : x^2 + y^2 + z^2 ≥ x * y * z   :=  by sorry
