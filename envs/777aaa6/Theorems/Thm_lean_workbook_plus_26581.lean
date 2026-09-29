-- Prove2me | Theorems.Thm_lean_workbook_plus_26581
-- name    : lean_workbook_plus_26581
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/76f110cf-0f20-4bcb-a465-2a16c1b2bfaa
-- statement:
--   When $m \geq 1$ , it is $3^{2^m}-1 = (3^{2^{m-1}}-1)(3^{2^{m-1}}+1)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26581 : ∀ m : ℕ, 1 ≤ m → 3^(2^m) - 1 = (3^(2^(m-1)) - 1) * (3^(2^(m-1)) + 1)   :=  by sorry
