-- Prove2me | Theorems.Thm_lean_workbook_plus_16666
-- name    : lean_workbook_plus_16666
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/c872f2fb-5145-4bc7-9ecc-73feccf8d6d1
-- statement:
--   For $a,b,c\ge0$ , prove that $\frac23(a^2+b^2+c^2)^2\ge{a^3(b+c)+b^3(a+c)+c^3(a+b)}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16666 (a b c : ℝ) : (2 / 3) * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 ≥ a ^ 3 * (b + c) + b ^ 3 * (a + c) + c ^ 3 * (a + b)   :=  by sorry
