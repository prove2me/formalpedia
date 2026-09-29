-- Prove2me | Theorems.Thm_lean_workbook_plus_17206
-- name    : lean_workbook_plus_17206
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/cad98eb1-e17d-4494-81d0-980d79c63921
-- statement:
--   $p-q=2\np^{3} -q^{3} =31106\ =\ ( p-q)\left( p^{2} +pq+q^{2}\right)\n( p-q)\left[( p-q)^{2} +3pq\right] =31106\npq=5183\np\ =\ x+1\nq=x-1\nx^{2} -1=5183\nx^{2} =5184
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17206  (p q : ℤ)
  (h₀ : p - q = 2)
  (h₁ : p^3 - q^3 = 31106) :
  p * q = 5183   :=  by sorry
