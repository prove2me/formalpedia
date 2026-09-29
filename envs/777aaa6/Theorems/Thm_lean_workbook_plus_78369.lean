-- Prove2me | Theorems.Thm_lean_workbook_plus_78369
-- name    : lean_workbook_plus_78369
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/5d7cd5c1-28b0-4d39-8136-c7a0c8b64c16
-- statement:
--   $(a^2+b^2+c^2 )(a^2b^2+b^2c^2+c^2a^2)\stackrel {am-gm}{\geq} 9a^2b^2c^2=9(4R\triangle)^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78369 (a b c : ℝ) (hab : a > 0 ∧ b > 0 ∧ c > 0) (habc : a + b > c) (hbc : b + c > a) (hca : a + c > b) : (a^2 + b^2 + c^2) * (a^2 * b^2 + b^2 * c^2 + c^2 * a^2) ≥ 9 * a^2 * b^2 * c^2   :=  by sorry
