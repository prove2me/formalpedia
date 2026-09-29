-- Prove2me | Theorems.Thm_lean_workbook_plus_43460
-- name    : lean_workbook_plus_43460
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/6735111d-23ad-47b3-a277-0cb403c17c83
-- statement:
--   It is well known that $4(a^2b+b^2c+c^2a+abc) \le \frac{16}{27}(a+b+c)^3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_43460 : ∀ a b c : ℝ, 4 * (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a + a * b * c) ≤ (16 / 27) * (a + b + c) ^ 3   :=  by sorry
