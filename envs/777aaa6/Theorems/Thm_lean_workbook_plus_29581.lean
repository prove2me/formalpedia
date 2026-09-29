-- Prove2me | Theorems.Thm_lean_workbook_plus_29581
-- name    : lean_workbook_plus_29581
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/8a9dc731-f7d4-4768-bd51-1eece642ee76
-- statement:
--   Prove that $a^2+b^2+c^2+\frac{abc(a+b+c)^2}{a^2b+b^2c+c^2a}\ge 2(ab+bc+ca)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29581 : ∀ a b c : ℝ, a^2 + b^2 + c^2 + (a * b * c * (a + b + c)^2) / (a^2 * b + b^2 * c + c^2 * a) ≥ 2 * (a * b + b * c + c * a)   :=  by sorry
