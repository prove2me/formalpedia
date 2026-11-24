-- Prove2me | solution 1 for SingularModuli.finite_family_table_fails
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T22:47:34.853074+00:00
-- url     : https://prove2.me/submissions/12681b82-3bdc-40bb-a91f-0522d82770ba

import Mathlib
import Definitions.Def_Cryptography_FactoringBarriers_CongruenceOfSquares
import Definitions.Def_Cryptography_SingularModuli_GcdCriterion
import Definitions.Def_Cryptography_SingularModuli_PrecomputationBarrier
import Definitions.Def_Cryptography_SingularModuli_RootCount

/-!
# The precomputed-table barrier for the singular moduli method (family form)

Proof: choose two distinct primes `p, q` exceeding both `M` and the total bit
mass `∑_{G ∈ F} ∑_{t ∈ T} |G(t)|` of the table.  Then for every entry the gcd
`gcd (G(t), pq)` is either `1` (when `G(t) ≠ 0`) or `pq` (when `G(t) = 0`), and
neither is a nontrivial divisor of `pq`.
-/

namespace SingularModuli

open Polynomial Finset FactoringBarriers

theorem solution (F : Finset (Polynomial ℤ)) (T : Finset ℤ) (M : ℕ) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ M < p ∧ M < q ∧
      ∀ G ∈ F, ∀ t ∈ T, ¬ NontrivialDivisor (p * q) (evalGcd G t (p * q)) := by
  classical
  obtain ⟨B₀, hB₀⟩ : ∃ B₀ : ℕ, ∀ G ∈ F, ∀ t ∈ T, (G.eval t).natAbs ≤ B₀ :=
    ⟨∑ G ∈ F, ∑ t ∈ T, (G.eval t).natAbs, by
      intro G hG t ht
      have h1 : (G.eval t).natAbs ≤ ∑ t ∈ T, (G.eval t).natAbs :=
        Finset.single_le_sum (f := fun t => (G.eval t).natAbs) (fun _ _ => Nat.zero_le _) ht
      have h2 : ∑ t ∈ T, (G.eval t).natAbs ≤ ∑ G ∈ F, ∑ t ∈ T, (G.eval t).natAbs :=
        Finset.single_le_sum (f := fun G => ∑ t ∈ T, (G.eval t).natAbs)
          (fun _ _ => Nat.zero_le _) hG
      exact h1.trans h2⟩
  obtain ⟨p, hpge, hpp⟩ := Nat.exists_infinite_primes (max M B₀ + 1)
  have hpM : M < p := by omega
  have hpB : B₀ < p := by omega
  obtain ⟨q, hqge, hqp⟩ := Nat.exists_infinite_primes (max p B₀ + 1)
  have hqM : M < q := by omega
  have hqB : B₀ < q := by omega
  have hpq : p ≠ q := by omega
  refine ⟨p, q, hpp, hqp, hpq, hpM, hqM, ?_⟩
  intro G hG t ht
  have hle : (G.eval t).natAbs ≤ B₀ := hB₀ G hG t ht
  by_cases h0 : G.eval t = 0
  · have hd : evalGcd G t (p * q) = p * q := by
      rw [evalGcd, h0, Int.gcd_def, Int.natAbs_zero, Int.natAbs_natCast]
      exact Nat.gcd_zero_left (p * q)
    rw [hd]
    exact fun h => absurd h.2.2 (lt_irrefl _)
  · have hpos : 0 < (G.eval t).natAbs :=
      Nat.pos_of_ne_zero fun h => h0 (Int.natAbs_eq_zero.mp h)
    have hd : evalGcd G t (p * q) = 1 := by
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
    rw [hd]
    exact fun h => absurd h.2.1 (lt_irrefl 1)

end SingularModuli

open SingularModuli Polynomial Finset FactoringBarriers

theorem solution (F : Finset (Polynomial ℤ)) (T : Finset ℤ) (M : ℕ) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ M < p ∧ M < q ∧
      ∀ G ∈ F, ∀ t ∈ T, ¬ NontrivialDivisor (p * q) (evalGcd G t (p * q)) :=
  SingularModuli.solution F T M

#print axioms solution
