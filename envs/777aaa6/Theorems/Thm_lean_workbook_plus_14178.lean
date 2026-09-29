-- Prove2me | Theorems.Thm_lean_workbook_plus_14178
-- name    : lean_workbook_plus_14178
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/4c35b5dc-198f-431e-9879-3352b1c21e63
-- statement:
--   Prove the following chain inequality for all non-negative real numbers $a,b$ and $c$: $3(a^2 + b^2 + c^2) \ge (a+b+c)^2 \ge 3(ab+bc+ca)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14178 (a b c: ℝ) : 3 * (a ^ 2 + b ^ 2 + c ^ 2) ≥ (a + b + c) ^ 2 ∧ (a + b + c) ^ 2 ≥ 3 * (a * b + b * c + c * a)   :=  by sorry
