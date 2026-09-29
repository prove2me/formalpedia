-- Prove2me | Theorems.Thm_lean_workbook_plus_6400
-- name    : lean_workbook_plus_6400
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/3a2b8f0c-0946-47bc-922c-58fcbc6b7773
-- statement:
--   $(3pq-1)=a(pq-p-q+1) ==> (a-3)pq+a+1=a(p+q)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6400  (p q a : ℂ)
  (h₀ : (3 * p * q - 1) = a * (p * q - p - q + 1)) :
  (a - 3) * p * q + a + 1 = a * (p + q)   :=  by sorry
