-- Prove2me | Theorems.Thm_lean_workbook_plus_56819
-- name    : lean_workbook_plus_56819
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/db1049c1-32e8-4f24-bd6c-a5b6cdd127a6
-- statement:
--   Looking at $(m^2+n^2-mn+m+n+1=0)$ , we can multiply by two on both sides to obtain: $(2m^2+2n^2-2mn+2m+2n+2=0)$ . Rearranging and factoring yields: $(m-n)^2+(m+1)^2+(n+1)^2=0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56819  (m n : ℤ)
  (h₀ : m^2 + n^2 - m * n + m + n + 1 = 0) :
  2 * m^2 + 2 * n^2 - 2 * m * n + 2 * m + 2 * n + 2 = 0   :=  by sorry
