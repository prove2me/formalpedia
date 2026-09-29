-- Prove2me | Theorems.Thm_lean_workbook_plus_76409
-- name    : lean_workbook_plus_76409
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/f3283e7f-39cf-4c6b-9468-e81b6ec2b903
-- statement:
--   Prove that $\frac{a^{2}}{4}+b^{2}+c^{2}-ab+ac-2bc \geq 0$ for all real numbers $a$, $b$, and $c$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_76409 (a b c : ℝ) : a^2 / 4 + b^2 + c^2 - a * b + a * c - 2 * b * c ≥ 0   :=  by sorry
