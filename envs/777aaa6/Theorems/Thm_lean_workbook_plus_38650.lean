-- Prove2me | Theorems.Thm_lean_workbook_plus_38650
-- name    : lean_workbook_plus_38650
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/ea3b5974-ef15-4965-aef9-b7b05cc5d053
-- statement:
--   Show that: $3xyz(x+y+z) \leq (xy+yz+zx)^{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38650 (x y z : ℝ) : 3 * x * y * z * (x + y + z) ≤ (x * y + y * z + z * x)^2   :=  by sorry
