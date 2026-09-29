-- Prove2me | Theorems.Thm_lean_workbook_plus_45278
-- name    : lean_workbook_plus_45278
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/7ad462d1-35d5-4237-94a7-ec840fd12acd
-- statement:
--   Prove that $x^x \geq 1 + x^2 - x$ for $x \geq 1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_45278 (hx: 1 ≤ x) : x^x ≥ 1 + x^2 - x   :=  by sorry
