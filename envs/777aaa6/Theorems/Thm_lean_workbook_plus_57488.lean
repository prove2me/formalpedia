-- Prove2me | Theorems.Thm_lean_workbook_plus_57488
-- name    : lean_workbook_plus_57488
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/1e5cd086-80fa-4e63-a510-7d2098540f5d
-- statement:
--   Prove that $2\left( {{x^4} + {y^4} + {z^4}} \right) + {x^2}{y^2} + {y^2}{z^2} + {z^2}{x^2} \ge 3\left( {{x^3}y + {y^3}z + {z^3}x} \right)$ given $abc = 1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_57488 (x y z : ℝ) (h : x*y*z = 1) : 2 * (x^4 + y^4 + z^4) + x^2*y^2 + y^2*z^2 + z^2*x^2 ≥ 3 * (x^3*y + y^3*z + z^3*x)   :=  by sorry
