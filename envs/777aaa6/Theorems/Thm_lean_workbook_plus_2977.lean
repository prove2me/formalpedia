-- Prove2me | Theorems.Thm_lean_workbook_plus_2977
-- name    : lean_workbook_plus_2977
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/d0a1577d-2f27-4f7d-a736-dd02d224c185
-- statement:
--   Let's say Harry is $h$ years old. Then Tom's age is $2h/3$ . Hence $h-2h/3 = 666$ , so $h=\boxed {1998}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2977  (h : ℝ)
  (h₀ : h - 2 * h / 3 = 666) :
  h = 1998   :=  by sorry
