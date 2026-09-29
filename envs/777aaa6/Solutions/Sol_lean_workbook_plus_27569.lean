-- Prove2me | solution 1 for lean_workbook_plus_27569
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:32:18.248386+00:00
-- url     : https://prove2.me/submissions/0074156a-7c54-4425-9278-43c578979e9e

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (G : Type*) [Group G] (n : ℕ) (M : ℕ → Set G) (hM : ∀ d : ℕ, M d = {x : G | orderOf x = d}) : ∀ d1 d2 : ℕ, d1 ≠ d2 → M d1 ∩ M d2 = ∅ := by
  intro d1 d2
  intros
  aesop (config := {maxRuleApplications := 120})
