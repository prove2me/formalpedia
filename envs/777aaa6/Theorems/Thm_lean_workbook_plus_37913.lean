-- Prove2me | Theorems.Thm_lean_workbook_plus_37913
-- name    : lean_workbook_plus_37913
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/576b2d74-2450-4247-a7ad-7986aea8275c
-- statement:
--   Prove the identity: \n\n\( (ax + by + cz + du)^2+(bx + cy + dz + au)^2+(cx + dy + az + bu)^2 + (dx + ay + bz + cu)^2 = \)\n\n\( (dx + cy + bz + au)^2+(cx + by + az + du)^2 +(bx + ay + dz + cu)^2 + (ax + dy + cz + bu)^2 \) .\n\nTreat $a,b,c,d$ like constants. Any monomial upon the expansion of any of the sides is either one of $x^2 , y^2 , z^2 , u^2$ , or of the form $xy , xz , yz , xu , yu , zu$ . Just show that the coefficient of each such term is equal.\n\nP.S. THIS IS no different than actually expanding.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37913  (b c d : ℝ) (x y z u : ℝ) :
  ((a * x + b * y + c * z + d * u)^2 + (b * x + c * y + d * z + a * u)^2 + (c * x + d * y + a * z + b * u)^2 + (d * x + a * y + b * z + c * u)^2) =
  ((d * x + c * y + b * z + a * u)^2 + (c * x + b * y + a * z + d * u)^2 + (b * x + a * y + d * z + c * u)^2 + (a * x + d * y + c * z + b * u)^2)   :=  by sorry
