-- Prove2me | Theorems.Thm_lean_workbook_plus_26361
-- name    : lean_workbook_plus_26361
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/e587693c-a88a-4087-8940-356f9a91f1c2
-- statement:
--   With x,y,z>0 we have $ \frac{a^3}{x}+\frac{b^3}{y}+\frac{c^3}{z}\geq\frac{a^3+b^3+c^3}{3(x+y+z)}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26361 (a b c x y z : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (a^3 / x + b^3 / y + c^3 / z) ≥ (a^3 + b^3 + c^3) / (3 * (x + y + z))   :=  by sorry
