-- Prove2me | Theorems.Thm_lean_workbook_plus_37051
-- name    : lean_workbook_plus_37051
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/d84c8ee7-451b-4251-91bb-08be2851f5cd
-- statement:
--   A divisor of $a$ clearly divides a multiple of $a$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37051 {a b : ℕ} (h : b ≠ 0) : a ∣ b → a ∣ b * a   :=  by sorry
