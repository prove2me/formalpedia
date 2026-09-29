-- Prove2me | Theorems.Thm_lean_workbook_plus_68861
-- name    : lean_workbook_plus_68861
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/6595ca43-b062-48f0-a4e3-0bc19815f2ed
-- statement:
--   Prove that: $ x^3+y^3+z^3+t^3\geq \frac{1}{2}$ given $(x;y;z;t) \in R$ such as $ x\geq-1$ ; $ y\geq-1$ ; $ z\geq-1$ ; $ t\geq-1$ and $ x+y+z+t=2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_68861 (x y z t : ℝ) (hx : x ≥ -1) (hy : y ≥ -1) (hz : z ≥ -1) (ht : t ≥ -1) (h : x + y + z + t = 2) : x ^ 3 + y ^ 3 + z ^ 3 + t ^ 3 ≥ 1 / 2   :=  by sorry
