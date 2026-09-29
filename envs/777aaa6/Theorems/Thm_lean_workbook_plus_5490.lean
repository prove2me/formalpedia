-- Prove2me | Theorems.Thm_lean_workbook_plus_5490
-- name    : lean_workbook_plus_5490
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/5585c80e-fc58-454a-a303-02dbdf95c394
-- statement:
--   Let $a,b$ be positive real numbers such that $a^5-b^3\geq 2a . $ Prove that $a^3\geq 2b$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_5490 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a^5 - b^3 ≥ 2 * a) : a^3 ≥ 2 * b   :=  by sorry
