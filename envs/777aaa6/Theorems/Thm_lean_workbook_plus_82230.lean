-- Prove2me | Theorems.Thm_lean_workbook_plus_82230
-- name    : lean_workbook_plus_82230
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/8bdf31db-b64d-4958-bf47-1a721c54c6b4
-- statement:
--   Add the 3 equality, we have ${a^2} + {b^2} + {c^2} = ab + bc + ca \Leftrightarrow \sum {{{\left( {a - b} \right)}^2}} = 0 \Leftrightarrow a = b = c$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_82230 (a b c: ℝ): a^2 + b^2 + c^2 = a * b + b * c + c * a ↔ a = b ∧ b = c   :=  by sorry
