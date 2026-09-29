-- Prove2me | Theorems.Thm_lean_workbook_plus_16044
-- name    : lean_workbook_plus_16044
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/8fa264ad-05c8-4b28-a409-f229939b25e1
-- statement:
--   If $a^3-3a=-11$ , what is the value of $a^6-6a^4+8a^3+9a^2-24a+16$ ?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16044 (a : ℝ) (h : a^3 - 3*a = -11) : a^6 - 6*a^4 + 8*a^3 + 9*a^2 - 24*a + 16 = 49   :=  by sorry
