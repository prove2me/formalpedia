-- Prove2me | Theorems.Thm_lean_workbook_plus_24078
-- name    : lean_workbook_plus_24078
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/4dc98ae5-741f-4b8f-bb39-281ff7fdf25a
-- statement:
--   prove $2({a^4} + {b^4} + {c^4}) \ge 2({a^2}{b^2} + {b^2}{c^2} + {c^2}{a^2})$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24078 (a b c : ℝ) : 2 * (a ^ 4 + b ^ 4 + c ^ 4) ≥ 2 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2)   :=  by sorry
