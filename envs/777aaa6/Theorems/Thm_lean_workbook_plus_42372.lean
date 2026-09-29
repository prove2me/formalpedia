-- Prove2me | Theorems.Thm_lean_workbook_plus_42372
-- name    : lean_workbook_plus_42372
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/6f6b91cc-9148-4531-bb58-89ae43659e11
-- statement:
--   Given $2 = x^2 + y^2 + z^2 \geq x^2 + y^2 \geq 2xy$, prove that $1 - xy \geq 0$, $1 - xz \geq 0$, and $1 - yz \geq 0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42372 (x y z : ℝ) (h₁ : 2 = x^2 + y^2 + z^2) (h₂ : x^2 + y^2 ≥ 2 * x * y) : 1 - x * y ≥ 0 ∧ 1 - x * z ≥ 0 ∧ 1 - y * z ≥ 0   :=  by sorry
