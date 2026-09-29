-- Prove2me | Theorems.Thm_lean_workbook_plus_49947
-- name    : lean_workbook_plus_49947
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/7bde2ffb-1775-4f5a-b27c-6e509115be71
-- statement:
--   Prove that $a^2+b^2+c^2+3(ab+bc+ca)\ge 4(ab+bc+ca)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49947 (a b c : ℝ) : a^2 + b^2 + c^2 + 3 * (a * b + b * c + c * a) ≥ 4 * (a * b + b * c + c * a)   :=  by sorry
