-- Prove2me | Theorems.Thm_lean_workbook_plus_5758
-- name    : lean_workbook_plus_5758
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/5bdb0a56-b255-400f-8627-519018bd75e9
-- statement:
--   Prove that $\sum_{cyc}(x+y)(y+z)=(x+y+z)^2+\frac{xyz}{x+y+z}+\frac{(x+y)(y+z)(z+x)}{x+y+z}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_5758 : ∀ x y z : ℝ, (x + y) * (y + z) + (y + z) * (z + x) + (z + x) * (x + y) = (x + y + z) ^ 2 + (xyz / (x + y + z)) + ((x + y) * (y + z) * (z + x)) / (x + y + z)   :=  by sorry
