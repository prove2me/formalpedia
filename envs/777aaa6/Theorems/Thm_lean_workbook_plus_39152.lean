-- Prove2me | Theorems.Thm_lean_workbook_plus_39152
-- name    : lean_workbook_plus_39152
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/adcf90ac-7427-4fdf-82f6-2cf742c6468a
-- statement:
--   Here is my approach: \n\nIt is easy to notice that: \n $ (a^2 + b^2)(b^2 + c^2)(c^2 + a^2)\ge \frac{8}{9}(a^2+b^2+c^2)(a^2b^2+b^2c^2+c^2a^2)$ \nNow by AM-GM: \n $ a^2+b^2+c^2\ge ab+bc+ca$ \n $ a^2b^2+b^2c^2+c^2a^2\ge \frac{1}{3}(ab+bc+ca)^2$ \nTherefore, $ 27LHS\ge 27.\frac{8}{9}(ab+bc+ca).\frac{1}{3}(ab+bc+ca)^2=RHS$ \nOur proof is completed.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39152 :  ∀ a b c : ℝ, (a^2 + b^2) * (b^2 + c^2) * (c^2 + a^2) ≥ (8/9) * (a^2 + b^2 + c^2) * (a^2 * b^2 + b^2 * c^2 + c^2 * a^2)   :=  by sorry
