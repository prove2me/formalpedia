-- Prove2me | solution 1 for lean_workbook_plus_15378
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:44:12.411294+00:00
-- url     : https://prove2.me/submissions/5d6d55a1-3c64-47bd-bd40-e58f4d1368ad

import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Order.Preorder.Finite
import Mathlib.Tactic

private theorem infinitely_many_quadratic_prime_divisors :
    Set.Infinite {p : ℕ | p.Prime ∧ ∃ n : ℕ, p ∣ 3 * n ^ 2 + 1} := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  have hF := Nat.factorial_pos N
  have hne : 3 * (N.factorial) ^ 2 + 1 ≠ 1 := by nlinarith
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
  refine ⟨p, ⟨hp, ⟨N.factorial, hpdvd⟩⟩, ?_⟩
  by_contra hle
  have hpf : p ∣ N.factorial := Nat.dvd_factorial hp.pos (by omega)
  have hterm : p ∣ 3 * (N.factorial) ^ 2 := by
    simpa only [pow_two] using
      dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hpf N.factorial) 3
  exact hp.not_dvd_one ((Nat.dvd_add_iff_right hterm).2 hpdvd)

theorem solution : Set.Infinite {p : ℕ | ∃ n : ℕ, p ∣ 3 * n ^ 2 + 1} := by
  exact infinitely_many_quadratic_prime_divisors.mono (fun _ hp => hp.2)
