-- Prove2me | Theorems.Thm_lean_workbook_plus_57779
-- name    : lean_workbook_plus_57779
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/35aa60cc-3d72-4310-be9b-562dff0cd3e6
-- statement:
--   Let $a,b,c$ be the sides of a triangle .Then prove that \n $\frac{a-b}{b+c} + \frac{b-c}{c+a} + \frac{c-a}{a+b} <0.5$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_57779 (a b c : ℝ) (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : (a - b) / (b + c) + (b - c) / (c + a) + (c - a) / (a + b) < 1 / 2   :=  by sorry
