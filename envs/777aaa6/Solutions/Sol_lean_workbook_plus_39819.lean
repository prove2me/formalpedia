-- Prove2me | solution 1 for lean_workbook_plus_39819
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T23:17:56.155166+00:00
-- url     : https://prove2.me/submissions/e1b3559e-66b0-4320-8481-3b855d57737b

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution : ∃ f : ℕ → ℕ × ℕ, f 1 = (1,1) ∧ f 2 = (2,1) ∧ f 3 = (1,2) ∧ f 4 = (3,1) ∧ f 5 = (2,2) ∧ f 6 = (1,3) ∧ f 7 = (4,1) := by
  let step : ℕ × ℕ → ℕ × ℕ := fun p => if p.1 = 1 then (p.2+1,1) else (p.1-1,p.2+1)
  let p : ℕ → ℕ × ℕ := Nat.rec (1,1) (fun _ r => step r)
  let f : ℕ → ℕ × ℕ := fun n => p (n-1)
  refine ⟨f, ?_⟩
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
