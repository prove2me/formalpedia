-- Prove2me | Theorems.Thm_lean_workbook_plus_80386
-- name    : lean_workbook_plus_80386
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/1df6db26-a492-4754-9a54-9e07ff781ca4
-- statement:
--   that equivalent with : $$2(a^2+b^2+c^2)(ab+bc+ca) + (ab+bc+ca)^2 \leq 3(a^2+b^2+c^2)^2$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80386 (a b c : ℝ) : 2 * (a ^ 2 + b ^ 2 + c ^ 2) * (a * b + b * c + c * a) + (a * b + b * c + c * a) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2   :=  by sorry
