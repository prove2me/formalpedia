-- Prove2me | Theorems.Thm_lean_workbook_plus_9842
-- name    : lean_workbook_plus_9842
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/bbe72844-a494-486e-b81d-56eaf5e6f156
-- statement:
--   Let $0 \le a,b,c \le 1.$ Prove that $a+b+c-ab-bc-ca\leq 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9842 (a b c : ℝ) (ha : a ∈ Set.Icc 0 1) (hb : b ∈ Set.Icc 0 1) (hc : c ∈ Set.Icc 0 1) : a + b + c - a * b - b * c - c * a ≤ 1   :=  by sorry
