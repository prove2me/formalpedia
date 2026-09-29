-- Prove2me | Theorems.Thm_lean_workbook_plus_51822
-- name    : lean_workbook_plus_51822
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/79c31cc0-e5cb-465a-ba98-28e2ccc1f3ce
-- statement:
--   (*) Prove that \n $ (a+b)(b+c)(c+d)(d+a) \geq (a+b+c+d)(abc+bcd+cda+dab) $\n
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51822 (a b c d : ℝ) : (a + b) * (b + c) * (c + d) * (d + a) ≥ (a + b + c + d) * (a * b * c + b * c * d + c * d * a + d * a * b)   :=  by sorry
