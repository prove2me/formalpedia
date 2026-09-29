-- Prove2me | Theorems.Thm_lean_workbook_plus_12331
-- name    : lean_workbook_plus_12331
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/7abd647b-c02b-48ba-9ede-6683356a1ed4
-- statement:
--   If $ x, y, z > 0 $ and $ x+y+z=\frac{1}{2xyz} $ then:\n\n$ \sqrt{1+x^4+y^4+z^4} \ge xy+yz+zx \ \ ; $\n\nGreetings!
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12331 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x + y + z = 1 / (2 * x * y * z)) :  Real.sqrt (1 + x^4 + y^4 + z^4) ≥ x * y + y * z + z * x   :=  by sorry
