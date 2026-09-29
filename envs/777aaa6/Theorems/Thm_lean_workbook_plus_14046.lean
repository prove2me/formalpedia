-- Prove2me | Theorems.Thm_lean_workbook_plus_14046
-- name    : lean_workbook_plus_14046
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/873f3ef8-bf9e-4cc8-b6a8-771737b7e6eb
-- statement:
--   same conditions: $\sqrt {{\frac {xy}{xy+z}}}+\sqrt {{\frac {yz}{yz+x}}}+\sqrt {{\frac {xz}{xz+y}}}\geq 1+4\,{\frac {xyz}{ \left( y+z \right) \left( z+x \right) \left( x+y \right) }}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14046 : ∀ x y z : ℝ, (Real.sqrt ((x * y) / (x * y + z)) + Real.sqrt ((y * z) / (y * z + x)) + Real.sqrt ((z * x) / (z * x + y)) ≥ 1 + 4 * (x * y * z) / ((y + z) * (z + x) * (x + y)))   :=  by sorry
