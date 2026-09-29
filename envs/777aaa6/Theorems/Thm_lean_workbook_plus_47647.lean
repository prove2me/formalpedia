-- Prove2me | Theorems.Thm_lean_workbook_plus_47647
-- name    : lean_workbook_plus_47647
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/833d5060-549e-4092-8565-f0a6f07b9ce0
-- statement:
--   Let $x,y,z,u,v,w \in R$ ,prove that \n\n $(x-u)^2+(y-v)^2+(z-w)^2 \geq $ \n $ \frac{1}{2}((x-z)(x-u-v+z)+(y-x)(y-v-w+x)+(z-y)(z-w-u+y))$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47647 (x y z u v w : ℝ) :
  (x - u) ^ 2 + (y - v) ^ 2 + (z - w) ^ 2 ≥
    1 / 2 * ((x - z) * (x - u - v + z) + (y - x) * (y - v - w + x) + (z - y) * (z - w - u + y))   :=  by sorry
