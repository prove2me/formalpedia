-- Prove2me | solution 1 for lean_workbook_plus_43083
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:04:57.190567+00:00
-- url     : https://prove2.me/submissions/b4e992a7-2c7a-4a54-9c4a-a2df25349658

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (f : ℕ → ℕ): (∀ a b : ℕ, f (a + b + a*b) = f (a*b)) ↔ ∃ c :ℕ, ∀ n : ℕ, f n = c := by
  constructor
  · intro h
    refine ⟨f 0,?_⟩
    intro n
    simpa using h n 0
  · rintro ⟨c,hc⟩ a b
    rw [hc,hc]
