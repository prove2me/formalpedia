-- Prove2me | solution 1 for ProofsInTheBook.Chapter01.chapter01_euclid
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-09-12T13:34:00.25706+00:00
-- url     : https://prove2.me/submissions/3af71e59-a38d-4668-8969-988b75d9e352

import Mathlib
import Mathlib.NumberTheory.LucasLehmer



/--
Chapter 1: Six proofs of the infinity of primes.
-/

theorem solution : Infinite {p : ℕ // p.Prime} := by
  classical
  rcases finite_or_infinite ({p : ℕ // p.Prime}) with hfin | hinf
  · letI : Fintype ({p : ℕ // p.Prime}) := Fintype.ofFinite ({p : ℕ // p.Prime})
    let N : ℕ := (Finset.univ : Finset {p : ℕ // p.Prime}).prod (fun p => (p : ℕ))
    have hN_pos : 0 < N := by
      unfold N
      exact Finset.prod_pos (fun p hp => p.2.pos)
    have h2dvd : (2 : ℕ) ∣ N := by
      unfold N
      exact
        (Finset.dvd_prod_of_mem
          (f := fun p : {p : ℕ // p.Prime} => (p : ℕ))
          (a := (⟨2, by decide⟩ : {p : ℕ // p.Prime}))
          (s := (Finset.univ : Finset {p : ℕ // p.Prime}))
          (by simp))
    have hN_ne : N + 1 ≠ 1 := by
      exact Nat.ne_of_gt (Nat.succ_le_succ hN_pos)
    have hN_ne : N + 1 ≠ 1 := by omega
    obtain ⟨q, hqprime, hqdvd⟩ := Nat.exists_prime_and_dvd hN_ne
    have hq_divides_factor : q ∣ N := by
      simpa [N] using
        (Finset.dvd_prod_of_mem
          (f := fun p : {p : ℕ // p.Prime} => (p : ℕ))
          (a := (⟨q, hqprime⟩ : {p : ℕ // p.Prime}))
          (s := (Finset.univ : Finset {p : ℕ // p.Prime}))
          (by simp))
    have hq_divides_one : q ∣ 1 := (Nat.dvd_add_iff_right hq_divides_factor).2 hqdvd
    exact False.elim (hqprime.not_dvd_one hq_divides_one)
  · exact hinf












