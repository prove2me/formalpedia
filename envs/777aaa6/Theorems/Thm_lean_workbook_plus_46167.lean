-- Prove2me | Theorems.Thm_lean_workbook_plus_46167
-- name    : lean_workbook_plus_46167
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/c085a351-cb10-4f19-b9f0-2a9fb91d7a13
-- statement:
--   Solution $\frac{\binom{5}{2}-\binom{3}{2}}{\binom{5}{2}}=\frac{7}{10}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46167 (h : 5 > 3) : (Nat.choose 5 2 - Nat.choose 3 2) / Nat.choose 5 2 = 7 / 10   :=  by sorry
