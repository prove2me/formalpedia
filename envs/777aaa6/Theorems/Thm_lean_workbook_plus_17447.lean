-- Prove2me | Theorems.Thm_lean_workbook_plus_17447
-- name    : lean_workbook_plus_17447
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/e47f0c37-c9e4-43cc-adb5-2a833e46612d
-- statement:
--   If $ 0 \le a, b, c, d \le 1 $ then: \n\n $ (1-a)(1-b)(1-c)(1-d)+ a+b+c+d \ge 1 \ \ ; $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17447 (a b c d : ℝ) (h1 : 0 ≤ a ∧ a ≤ 1) (h2 : 0 ≤ b ∧ b ≤ 1) (h3 : 0 ≤ c ∧ c ≤ 1) (h4 : 0 ≤ d ∧ d ≤ 1) : (1 - a) * (1 - b) * (1 - c) * (1 - d) + a + b + c + d ≥ 1   :=  by sorry
