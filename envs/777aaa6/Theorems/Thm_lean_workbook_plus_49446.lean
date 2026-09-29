-- Prove2me | Theorems.Thm_lean_workbook_plus_49446
-- name    : lean_workbook_plus_49446
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/657dbfd2-a26d-4e51-a0ad-19c4eea1a9e0
-- statement:
--   Hence, $ P \equiv 875 (mod 1000) $ . This is equivalent to saying $ P $ has $ 875 $ as its last three digits.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49446  (p : ℕ)
  (h₀ : p ≡ 875 [MOD 1000]) :
  p ≡ 875 [MOD 10^3]   :=  by sorry
