-- Prove2me | Theorems.Thm_lean_workbook_plus_21701
-- name    : lean_workbook_plus_21701
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/5722e999-80d4-4f65-95f4-875f708cf577
-- statement:
--   $nyz \ge 2x \implies \frac{n}{2} \ge \frac{x}{yz}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21701 (n x y z : ℝ) (hn : n > 0) (hx : x > 0) (hy : y > 0) (hz : z > 0) (h : n * y * z ≥ 2 * x) : n / 2 ≥ x / (y * z)   :=  by sorry
