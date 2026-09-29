-- Prove2me | Theorems.Thm_lean_workbook_plus_61945
-- name    : lean_workbook_plus_61945
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/cd5ab11f-d651-4b74-afd3-8f41f5799000
-- statement:
--   The probability of choosing two red balls is $\frac{20\cdot 19}{32\cdot 31}=\frac{95}{248}$ . The probability of choosing two blue balls is $\frac{12\cdot 11}{32\cdot 31}=\frac{33}{248}$ . Adding, we get the probability is $\frac{128}{248}=\frac{16}{31}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61945 :
  (20 * 19 / (32 * 31) + 12 * 11 / (32 * 31)) = 16 / 31   :=  by sorry
