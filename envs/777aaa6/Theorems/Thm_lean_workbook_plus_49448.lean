-- Prove2me | Theorems.Thm_lean_workbook_plus_49448
-- name    : lean_workbook_plus_49448
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/e682925b-5b13-455b-b5d4-b45da1a5df00
-- statement:
--   Show that if $ a|b$ , $ b|c$ , and $ c|a$ , then $ a=b=c$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49448 : ∀ {a b c : ℕ}, a ∣ b ∧ b ∣ c ∧ c ∣ a → a = b ∧ b = c ∧ c = a   :=  by sorry
