-- Prove2me | solution 1 for lean_workbook_plus_29794
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:18:03.830076+00:00
-- url     : https://prove2.me/submissions/2da62707-de80-44ec-95a2-a5ad0c4f0ecb

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ∀ m : ℕ, ∃ x : ℕ, x > m ∧ x % 6 = 3 := by
  intro m
  refine ⟨6*(m+1)+3,by omega,?_⟩
  omega
