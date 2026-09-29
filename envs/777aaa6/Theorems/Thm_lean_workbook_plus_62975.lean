-- Prove2me | Theorems.Thm_lean_workbook_plus_62975
-- name    : lean_workbook_plus_62975
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/c0214a64-eade-4916-898c-54a662b4f115
-- statement:
--   Hence, required no. = $\binom{9}{4}\cdot \frac{5!}{2!\cdot 2!} = \frac{9!}{2!\cdot 2!\cdot 4!}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62975 :
  Nat.choose 9 4 * (5! / (2! * 2!)) = 9! / (2! * 2! * 4!)   :=  by sorry
