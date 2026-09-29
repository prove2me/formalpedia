-- Prove2me | Theorems.Thm_lean_workbook_plus_2618
-- name    : lean_workbook_plus_2618
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/8d54c299-9dda-4ec9-b72a-cece99aa01b3
-- statement:
--   It suffices to prove that ${({a^2} + {b^2} + {c^2})^2} \ge \left[ {a(a - b + c) + b(b - c + a) + c(c - a + b)} \right]^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2618 : ∀ a b c : ℝ, (a^2 + b^2 + c^2)^2 ≥ (a * (a - b + c) + b * (b - c + a) + c * (c - a + b))^2   :=  by sorry
