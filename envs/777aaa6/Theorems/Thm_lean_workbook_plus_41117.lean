-- Prove2me | Theorems.Thm_lean_workbook_plus_41117
-- name    : lean_workbook_plus_41117
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/7dde8e0b-2020-48f7-b16e-ef0d952de2a5
-- statement:
--   Let $a=2m+1$ and $b=2n+1$, where $m, n \in \mathbb{Z}$. Show that $a^2-b^2$ is divisible by $8$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_41117 (m n : ℤ) : (2*m+1)^2 - (2*n+1)^2 ≡ 0 [ZMOD 8]   :=  by sorry
