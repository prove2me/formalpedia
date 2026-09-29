-- Prove2me | Theorems.Thm_lean_workbook_plus_78779
-- name    : lean_workbook_plus_78779
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/24728918-e190-44f0-9687-2a88fa9522bb
-- statement:
--   If $ a , b , c \in [0,1]$ , prove that : $ ab + bc + ca \leq 2abc + 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78779 (a b c : ℝ) (ha : a ∈ Set.Icc 0 1) (hb : b ∈ Set.Icc 0 1) (hc : c ∈ Set.Icc 0 1) : a * b + b * c + c * a ≤ 2 * a * b * c + 1   :=  by sorry
