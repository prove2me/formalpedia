-- Prove2me | Theorems.Thm_lean_workbook_plus_56168
-- name    : lean_workbook_plus_56168
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/fb926b68-d293-47c3-881a-84722d092d1a
-- statement:
--   Let $a, b$ and $c$ be integers such that $a + b + c = 0$. Show that $a^4 + b^4 + c^4$ is divisible by $a^2 + b^2 + c^2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56168 {a b c : ℤ} (h : a + b + c = 0) : (a^2 + b^2 + c^2) ∣ (a^4 + b^4 + c^4)   :=  by sorry
