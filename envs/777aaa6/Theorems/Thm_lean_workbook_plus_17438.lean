-- Prove2me | Theorems.Thm_lean_workbook_plus_17438
-- name    : lean_workbook_plus_17438
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/4a8a3b2f-6ecb-4bb9-873a-64b281537f02
-- statement:
--   Prove (or disprove) that for all integers $m$ , $m^5-m\equiv 0 \mod 5.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17438 (m : ℤ) : m^5 - m ≡ 0 [ZMOD 5]   :=  by sorry
