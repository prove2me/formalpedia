-- Prove2me | solution 1 for SingularModuli.precomputed_table_returns_one
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T22:47:35.440292+00:00
-- url     : https://prove2.me/submissions/b2672b52-327b-4ef2-a2ff-e75e8d237e6c

import Mathlib
import Definitions.Def_Cryptography_FactoringBarriers_CongruenceOfSquares
import Definitions.Def_Cryptography_SingularModuli_GcdCriterion
import Definitions.Def_Cryptography_SingularModuli_PrecomputationBarrier
import Definitions.Def_Cryptography_SingularModuli_RootCount

namespace SingularModuli

open Polynomial Finset FactoringBarriers

theorem solution (H : Polynomial ℤ) (T : Finset ℤ) (M : ℕ)
    (hT : ∀ t ∈ T, H.eval t ≠ 0) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ M < p ∧ M < q ∧
      ∀ t ∈ T, evalGcd H t (p * q) = 1 := by
  classical
  obtain ⟨B₀, hB₀⟩ : ∃ B₀ : ℕ, ∀ t ∈ T, (H.eval t).natAbs ≤ B₀ :=
    ⟨∑ t ∈ T, (H.eval t).natAbs, fun t ht =>
      Finset.single_le_sum (f := fun t => (H.eval t).natAbs) (fun _ _ => Nat.zero_le _) ht⟩
  obtain ⟨p, hpge, hpp⟩ := Nat.exists_infinite_primes (max M B₀ + 1)
  have hpM : M < p := by omega
  have hpB : B₀ < p := by omega
  obtain ⟨q, hqge, hqp⟩ := Nat.exists_infinite_primes (max p B₀ + 1)
  have hqM : M < q := by omega
  have hqB : B₀ < q := by omega
  have hpq : p ≠ q := by omega
  refine ⟨p, q, hpp, hqp, hpq, hpM, hqM, ?_⟩
  intro t ht
  have hle : (H.eval t).natAbs ≤ B₀ := hB₀ t ht
  have hpos : 0 < (H.eval t).natAbs :=
    Nat.pos_of_ne_zero fun h => hT t ht (Int.natAbs_eq_zero.mp h)
  rw [evalGcd, Int.gcd_def, Int.natAbs_natCast]
  rw [← Nat.coprime_iff_gcd_eq_one, Nat.coprime_mul_iff_right]
  constructor
  · rw [Nat.coprime_comm, hpp.coprime_iff_not_dvd]
    intro hdiv
    have := Nat.le_of_dvd hpos hdiv
    omega
  · rw [Nat.coprime_comm, hqp.coprime_iff_not_dvd]
    intro hdiv
    have := Nat.le_of_dvd hpos hdiv
    omega

end SingularModuli

open SingularModuli Polynomial Finset FactoringBarriers

theorem solution (H : Polynomial ℤ) (T : Finset ℤ) (M : ℕ)
    (hT : ∀ t ∈ T, H.eval t ≠ 0) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ M < p ∧ M < q ∧
      ∀ t ∈ T, evalGcd H t (p * q) = 1 :=
  SingularModuli.solution H T M hT

#print axioms solution
