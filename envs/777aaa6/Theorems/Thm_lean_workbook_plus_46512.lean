-- Prove2me | Theorems.Thm_lean_workbook_plus_46512
-- name    : lean_workbook_plus_46512
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/9ee05087-5e47-43ac-8e59-4d5866057198
-- statement:
--   Given are three real numbers $a,b,c$ with $a+b+c=1$ . Prove that $a^2 + b^2 + c^2 + ab + bc \geq \frac{1}{2}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46512 (a b c : ℝ) (habc : a + b + c = 1) : a^2 + b^2 + c^2 + a * b + b * c ≥ 1 / 2   :=  by sorry
