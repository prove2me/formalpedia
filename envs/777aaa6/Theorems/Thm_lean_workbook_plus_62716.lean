-- Prove2me | Theorems.Thm_lean_workbook_plus_62716
-- name    : lean_workbook_plus_62716
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/2bbb7038-53eb-43cb-a7cb-6807b6e679d2
-- statement:
--   In the interval $[m^2,(m+1)^2]$ , there are $(m+1)^2 - m^2 + 1 =2(m+1)$ numbers.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62716  (m : ℕ) :
  ((m + 1)^2 - m^2 + 1) = 2 * (m + 1)   :=  by sorry
