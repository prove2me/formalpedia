-- Prove2me | solution 1 for lean_workbook_plus_60497
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:48:10.847828+00:00
-- url     : https://prove2.me/submissions/4206c109-7276-495e-814c-e2e806f44fef

import Mathlib.NumberTheory.LSeries.PrimesInAP

theorem arbitrarily_large_prime_progression_coefficients (n r : ℕ)
    (hn : 0 < n) (hcop : r.Coprime n) (L : ℕ) :
    ∃ k : ℕ, L < k ∧ (n * k + r).Prime := by
  obtain ⟨P, hP, hp, hmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq (r + n * L) hn.ne' hcop
  have hrP : r ≤ P := by omega
  obtain ⟨k, hk⟩ := (Nat.modEq_iff_exists_eq_add hrP).mp hmod.symm
  refine ⟨k, ?_, ?_⟩
  · by_contra h
    have hkle : k ≤ L := by omega
    have := Nat.mul_le_mul_left n hkle
    omega
  · simpa only [hk, add_comm r] using hp

theorem infinitely_many_prime_progression_coefficients (n r : ℕ)
    (hn : 0 < n) (hcop : r.Coprime n) :
    Set.Infinite {k : ℕ | 0 < k ∧ (n * k + r).Prime} := by
  apply Set.infinite_iff_exists_gt.mpr
  intro L
  obtain ⟨k, hk, hp⟩ := arbitrarily_large_prime_progression_coefficients n r hn hcop L
  exact ⟨k, ⟨by omega, hp⟩, hk⟩

theorem prime_residue_positive_coefficient (n p : ℕ) (hp : p.Prime)
    (hcop : n.Coprime p) (L : ℕ) :
    ∃ P k : ℕ, P.Prime ∧ L < k ∧ n * k + p = P := by
  have hn : 0 < n := by
    by_contra h
    have hn0 : n = 0 := by omega
    have hp1 : p = 1 := by simpa only [hn0, Nat.coprime_zero_left] using hcop
    exact hp.ne_one hp1
  obtain ⟨k, hk, hP⟩ := arbitrarily_large_prime_progression_coefficients n p hn hcop.symm L
  exact ⟨n * k + p, k, hP, hk, rfl⟩

theorem solution (n p : ℕ) (hp : p.Prime) (h : Nat.Coprime n p) :
    ∃ P k : ℕ, P.Prime ∧ n * k + p = P := by
  obtain ⟨P, k, hP, _hk, he⟩ := prime_residue_positive_coefficient n p hp h 0
  exact ⟨P, k, hP, he⟩
