-- Prove2me | Theorems.Thm_lean_workbook_plus_35669
-- name    : lean_workbook_plus_35669
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/59d796f8-c05e-4c77-9b34-f5c3b3a568e4
-- statement:
--   Prove that $a(3a-b+c)+(b)(3b-c+a)+(c)(3c-a+b)=3\left(a^{2}+b^{2}+c^{2}\right)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_35669 (a b c : ℝ) : a * (3 * a - b + c) + b * (3 * b - c + a) + c * (3 * c - a + b) = 3 * (a ^ 2 + b ^ 2 + c ^ 2)   :=  by sorry
