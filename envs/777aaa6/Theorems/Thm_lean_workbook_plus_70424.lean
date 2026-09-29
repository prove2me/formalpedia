-- Prove2me | Theorems.Thm_lean_workbook_plus_70424
-- name    : lean_workbook_plus_70424
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/892b41ce-a5a8-4b6a-b3db-b3c6495f507d
-- statement:
--   And by AM-GM we have $2\left( {ab + bc + cd + da + ac + bd} \right) \le 3\left( {{a^2} + {b^2} + {c^2} + {d^2}} \right)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70424 {a b c d : ℝ} : 2 * (a * b + b * c + c * d + d * a + a * c + b * d) ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2)   :=  by sorry
