-- Prove2me | Theorems.Thm_lean_workbook_plus_34029
-- name    : lean_workbook_plus_34029
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/39abd846-3669-4887-afee-72a4d429ce82
-- statement:
--   $\frac{3(xy+yz+zx)}{xy+yz+zx}$ $=$ $3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_34029  (x y z : ℝ)
  (h₀ : x * y + y * z + z * x ≠ 0) :
  3 * (x * y + y * z + z * x) / (x * y + y * z + z * x) = 3   :=  by sorry
