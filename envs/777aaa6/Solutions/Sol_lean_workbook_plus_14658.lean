-- Prove2me | solution 1 for lean_workbook_plus_14658
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:55:57.304399+00:00
-- url     : https://prove2.me/submissions/85bc230b-ead2-4127-ae7f-6026fb211ed7

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (k m n : ℤ)
  (h₀ : Odd k ∧ Odd m ∧ Odd n)
  (h₁ : 4 ∣ (k + m))
  (h₂ : 4 ∣ (m + n)) :
  ¬ 4 ∣ (k + n) := by
  intros
  grind
