-- Prove2me | Theorems.Thm_lean_workbook_plus_38068
-- name    : lean_workbook_plus_38068
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/6216b4dc-ed49-4a89-a143-b8060dccabdf
-- statement:
--   Prove that $x^{ab} = (x^a)^b$ for any $x \geq 0$ and any real numbers $a$ and $b$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38068 {x : ℝ} (hx : 0 ≤ x) (a b : ℝ) : x ^ (a * b) = (x ^ a) ^ b   :=  by sorry
