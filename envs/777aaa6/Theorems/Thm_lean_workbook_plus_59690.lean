-- Prove2me | Theorems.Thm_lean_workbook_plus_59690
-- name    : lean_workbook_plus_59690
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/8b89f402-75df-4a21-b4e9-c3d4b0a0e42c
-- statement:
--   The first inequality is equivalent to: $\sqrt{\frac{2}{3}+\frac{abc}{a^3+b^3+c^3}}\ge\sqrt{\frac{bc+ca+ab}{a^2+b^2+c^2}}\Leftrightarrow \frac{1}{3}-\frac{abc}{a^3+b^3+c^3}\le\frac{a^2+b^2+c^2-ab-bc-ca}{a^2+b^2+c^2}\Leftrightarrow \frac{(a+b+c)(a^2+b^2+c^2-ab-bc-ca)}{3(a^3+b^3+c^3)}\le\frac{a^2+b^2+c^2-ab-bc-ca}{a^2+b^2+c^2}\Leftrightarrow (a^2+b^2+c^2-ab-bc-ca)(\frac{1}{a^2+b^2+c^2}-\frac{a+b+c}{3(a^3+b^3+c^3)})\ge 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59690 :  ∀ a b c : ℝ, (a^2 + b^2 + c^2 - a * b - b * c - c * a) * (1 / (a^2 + b^2 + c^2) - (a + b + c) / (3 * (a^3 + b^3 + c^3))) ≥ 0   :=  by sorry
