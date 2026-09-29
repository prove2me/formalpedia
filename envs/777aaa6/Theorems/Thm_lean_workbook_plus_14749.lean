-- Prove2me | Theorems.Thm_lean_workbook_plus_14749
-- name    : lean_workbook_plus_14749
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/049b78d5-959a-4fd8-8f68-23609faa2370
-- statement:
--   Given real numbers $ x,y,z\geq -1$ satisfying $ x^3 +y^3 + z^3 \geq x^2 + y^2 + z^2$ , prove that $ x^5 + y^5 + z^5 \geq x^2 + y^2 + z^2$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14749 (x y z : ℝ) (hx : x ≥ -1) (hy : y ≥ -1) (hz : z ≥ -1) (h : x^3 + y^3 + z^3 ≥ x^2 + y^2 + z^2) : x^5 + y^5 + z^5 ≥ x^2 + y^2 + z^2   :=  by sorry
