-- Prove2me | Theorems.Thm_lean_workbook_plus_14748
-- name    : lean_workbook_plus_14748
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/5a47e134-6ff0-4663-8dcd-7c8bafc030e6
-- statement:
--   Prove that \(\sqrt {a^{1 - a}b^{1 - b}c^{1 - c}}\ge \dfrac{1}{3}\) for \( a,b,c\in R^ +\) such that \( a + b + c = 1\)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14748 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 1) : (a^(1 - a) * b^(1 - b) * c^(1 - c))^(1 / 3) ≥ 1 / 3   :=  by sorry
