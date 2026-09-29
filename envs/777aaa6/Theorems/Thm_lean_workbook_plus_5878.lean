-- Prove2me | Theorems.Thm_lean_workbook_plus_5878
-- name    : lean_workbook_plus_5878
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/1eb93646-a3d1-41fd-bc03-23823fac33ee
-- statement:
--   Let $a,b,c$ be non-negative real numbers. Prove that:\n\n $$ \sqrt[3]{a^2+ab+b^2}+\sqrt[3]{b^2+bc+c^2}+\sqrt[3]{c^2+ca+a^2} \geq 3\sqrt[3]{ab+bc+ca}$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_5878 (a b c : ℝ) : (a^2 + ab + b^2)^(1/3) + (b^2 + bc + c^2)^(1/3) + (c^2 + ca + a^2)^(1/3) ≥ 3 * (ab + bc + ca)^(1/3)   :=  by sorry
