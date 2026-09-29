-- Prove2me | Theorems.Thm_lean_workbook_plus_14772
-- name    : lean_workbook_plus_14772
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/2ba1f446-1197-4cfd-8be5-2c9561336d85
-- statement:
--   Given x, y are positive integers such that ${{x}^2-xy+{y}^2}\mid{xy(x-y)}$. Prove that ${gcd(x,y)}\ge{\sqrt[3]{xy}}$. Where does the equation hold?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14772 (x y : ℤ) (h : x > 0 ∧ y > 0) (h2 : (x^2 - x*y + y^2) ∣ (x*y*(x - y))) : (Int.gcd x y) ≥ (xy)^(1/3)   :=  by sorry
