-- Prove2me | Theorems.Thm_lean_workbook_plus_40209
-- name    : lean_workbook_plus_40209
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/6f1f914a-2ec7-4b7a-83e5-0dae148521b1
-- statement:
--   Prove that if $a, b$ are integers and $a \mid b$, then $a^2 \mid b^2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40209 {a b : ℤ} (h : a ∣ b) : a^2 ∣ b^2   :=  by sorry
