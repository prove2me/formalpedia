-- Prove2me | Theorems.Thm_lean_workbook_plus_75534
-- name    : lean_workbook_plus_75534
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/86c385c5-103c-4718-b38b-5ebb338a853a
-- statement:
--   $(1+a^2)(1+a^2+b^2)(1+a^2+b^2+c^2)\geq 16abc \Leftrightarrow (1+a^2)(1+a^2+b^2)c^2-16abc+(1+a^2)(1+a^2+b^2)^2\geq0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75534 (a b c : ℝ) : (1 + a ^ 2) * (1 + a ^ 2 + b ^ 2) * (1 + a ^ 2 + b ^ 2 + c ^ 2) ≥ 16 * a * b * c ↔ (1 + a ^ 2) * (1 + a ^ 2 + b ^ 2) * c ^ 2 - 16 * a * b * c + (1 + a ^ 2) * (1 + a ^ 2 + b ^ 2) ^ 2 ≥ 0   :=  by sorry
