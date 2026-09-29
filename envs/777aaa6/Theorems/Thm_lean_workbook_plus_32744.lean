-- Prove2me | Theorems.Thm_lean_workbook_plus_32744
-- name    : lean_workbook_plus_32744
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/9ba5341a-0143-4de4-92da-4bb7762b9a7f
-- statement:
--   $=2abc\left( 2\left( a^{2}+b^{2}+c^{2} \right)+b^{2}+c^{2}+bc \right)=abc\left( 4\left( a^{2}+b^{2}+c^{2} \right)+2\left( b^{2}+c^{2}+bc \right) \right)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32744 (a b c : ℝ) : 2 * a * b * c * (2 * (a ^ 2 + b ^ 2 + c ^ 2) + b ^ 2 + c ^ 2 + b * c) = a * b * c * (4 * (a ^ 2 + b ^ 2 + c ^ 2) + 2 * (b ^ 2 + c ^ 2 + b * c))   :=  by sorry
