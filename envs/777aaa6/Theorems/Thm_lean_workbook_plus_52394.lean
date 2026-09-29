-- Prove2me | Theorems.Thm_lean_workbook_plus_52394
-- name    : lean_workbook_plus_52394
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/d2037bc9-7a4c-48e1-96ea-47e09dc00591
-- statement:
--   Let $a$ be a real number such that $2a^6+a^2=\frac{3}{2}+2a^4$ . Prove that $a^8>1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52394 (a : ℝ) (h : 2*a^6 + a^2 = 3/2 + 2*a^4) : a^8 > 1   :=  by sorry
