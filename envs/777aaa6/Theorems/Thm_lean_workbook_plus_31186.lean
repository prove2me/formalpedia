-- Prove2me | Theorems.Thm_lean_workbook_plus_31186
-- name    : lean_workbook_plus_31186
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/1c52a662-db43-4984-8c38-f529757a4a0c
-- statement:
--   Examine the expression $\Delta = 100{\left( {{a^2} + {b^2} + {c^2}} \right)^2} - 192\left( {{a^2}{b^2} + {b^2}{c^2} + {c^2}{a^2}} \right)$ and determine if it is always non-negative.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31186 :  ∀ a b c : ℝ, 100 * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 - 192 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) ≥ 0   :=  by sorry
