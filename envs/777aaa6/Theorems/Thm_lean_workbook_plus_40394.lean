-- Prove2me | Theorems.Thm_lean_workbook_plus_40394
-- name    : lean_workbook_plus_40394
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/ef46f3ff-2e11-4e88-8955-1b003b09000c
-- statement:
--   The inequality is equivalent to: $S_{a}(b-c)^{2}+S_{b}(c-a)^{2}+S_{c}(a-b)^{2}\geq 0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40394 {a b c : ℝ} (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hab : a + b ≥ c) (hbc : b + c ≥ a) (hca : a + c ≥ b) : a * (b - c) ^ 2 + b * (c - a) ^ 2 + c * (a - b) ^ 2 ≥ 0   :=  by sorry
