-- Prove2me | Theorems.Thm_lean_workbook_plus_31804
-- name    : lean_workbook_plus_31804
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/68642d61-45d8-4117-8576-12f212a86452
-- statement:
--   Stronger ${x}^{3}+{y}^{3}+{z}^{3}\geq-3\,xyz+2\,{\frac { \left( xy+xz+yz \right) \left( {x}^{2}+{y}^{2}+{z}^{2} \right) }{x+y+z}}\geq \left( x+y+z \right) \left( xy+xz+yz \right) -6\,xyz$ ${x}^{3}+{y}^{3}+{z}^{3}- \left( x+y+z \right) \left( xy+xz+yz \right) +6\,xyz={\it \sum} \left( x \left( x-y \right) \left( x-z \right) \right)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31804 :  ∀ x y z : ℝ, x^3 + y^3 + z^3 - (x + y + z) * (x * y + x * z + y * z) + 6 * x * y * z = (x * (x - y) * (x - z) + y * (y - z) * (y - x) + z * (z - x) * (z - y))   :=  by sorry
