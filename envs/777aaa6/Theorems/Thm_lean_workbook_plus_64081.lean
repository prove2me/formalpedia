-- Prove2me | Theorems.Thm_lean_workbook_plus_64081
-- name    : lean_workbook_plus_64081
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/390caa0d-36bd-43b1-ad2d-40505ea941bc
-- statement:
--   Prove that: \n $-{{a}^{3}}+{{a}^{2}}b+a{{b}^{2}}-{{b}^{3}}+{{a}^{2}}c-2abc+{{b}^{2}}c+a{{c}^{2}}+b{{c}^{2}}-{{c}^{3}}$ \n $=(a+b-c)(a+c-b)(b+c-a)$ \n Direct Proof Please!!!
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64081 : ∀ a b c : ℝ, -a^3 + a^2 * b + a * b^2 - b^3 + a^2 * c - 2 * a * b * c + b^2 * c + a * c^2 + b * c^2 - c^3 = (a + b - c) * (a + c - b) * (b + c - a)   :=  by sorry
