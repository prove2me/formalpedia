-- Prove2me | solution 1 for lean_workbook_plus_74285
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T20:12:05.675207+00:00
-- url     : https://prove2.me/submissions/231db266-5e4b-4799-bdb6-b0c56bfd68df

import Mathlib
set_option autoImplicit false

theorem solution : ¬ (∀ p : ℕ → ℚ, p 1 = 1 / 6 → (∀ n, p (n + 1) = 1 / 6 * (1 + p n)) → p 5 = 33 / 38) := by
  intro h
  let p : ℕ → ℚ := fun n => Nat.rec 0 (fun _ v => 1 / 6 * (1 + v)) n
  have hp : p 1 = 1 / 6 := by norm_num [p]
  have hrec : ∀ n, p (n + 1) = 1 / 6 * (1 + p n) := by
    intro n
    rfl
  have hp5 : p 5 = 1555 / 7776 := by
    have h2 := hrec 1
    have h3 := hrec 2
    have h4 := hrec 3
    have h5 := hrec 4
    norm_num at h2 h3 h4 h5
    rw [h5, h4, h3, h2, hp]
    norm_num
  have bad := h p hp hrec
  rw [hp5] at bad
  norm_num at bad

#print axioms solution
