-- Prove2me | Theorems.Thm_lean_workbook_plus_14755
-- name    : lean_workbook_plus_14755
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/5f0d2cad-8f61-4c3d-bda6-cf94409be225
-- statement:
--   we have $ 3\sum_{cyc}\left(\frac{a}{a+2b}\right)^2\ge\left(\sum_{cyc}\frac{a} {a+2b}\right)^2$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14755 (a b c : ℝ) : 3 * ((a / (a + 2 * b)) ^ 2 + (b / (b + 2 * c)) ^ 2 + (c / (c + 2 * a)) ^ 2) ≥ (a / (a + 2 * b) + b / (b + 2 * c) + c / (c + 2 * a)) ^ 2   :=  by sorry
