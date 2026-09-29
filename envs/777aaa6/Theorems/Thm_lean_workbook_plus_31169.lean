-- Prove2me | Theorems.Thm_lean_workbook_plus_31169
-- name    : lean_workbook_plus_31169
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/0c775a37-46c7-4532-b492-d0c76a40731a
-- statement:
--   $\frac{(y+z)^2(z+x)}{(2x+y+z)^2}\ge \frac{zy}{x+y}\Leftrightarrow \frac{(x+y)(z+x)}{(2x+y+z)^2}\ge \frac{zy}{(y+z)^2}\Leftrightarrow \frac{(2x+y+z)^2}{(x+y)(z+x)}\leq \frac{(y+z)^2}{yz}\Leftrightarrow \frac{(2x+y+z)^2-4(x+y)(z+x)}{(x+y)(z+x)}\leq \frac{(y+z)^2-4yz}{yz}\Leftrightarrow \frac{(y-z)^2}{(x+y)(z+x)}\leq \frac{(y-z)^2}{yz}\Leftrightarrow (y-z)^2(\frac{x^2+xy+xz}{(x+y)(z+x)yz})\ge 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31169 : ∀ x y z : ℝ, (y - z) ^ 2 * (x ^ 2 + x * y + x * z) / ((x + y) * (z + x) * y * z) ≥ 0   :=  by sorry
