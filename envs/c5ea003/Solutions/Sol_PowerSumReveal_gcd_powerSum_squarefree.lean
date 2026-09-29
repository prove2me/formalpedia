-- Prove2me | solution 1 for PowerSumReveal.gcd_powerSum_squarefree
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T00:12:12.661265+00:00
-- url     : https://prove2.me/submissions/21a8f73f-fb49-4631-9b23-dffd0f85b7d7

-- Sol generated from Combinatorics/PowerSumFactorReveal.lean
import Mathlib
import Definitions.Def_Combinatorics_PowerSumFactorReveal
import Theorems.Thm_PowerSumReveal_cast_powerSum

/-!
# Power-sum factor reveal for squarefree moduli

For a modulus `N` let
`F(N, k) = ∑_{a = 1}^{N} a ^ k`  (`PowerSumReveal.powerSum`).

The central observation is a **complete local computation**: if `p` is a prime
dividing `N` and `k ≥ 1`, then modulo `p` the interval `{1, …, N}` covers each
residue class exactly `N / p` times, so

`F(N, k) ≡ (N / p) · ∑_{x ∈ ZMod p} x ^ k ≡ (N / p) · (if (p-1) ∣ k then -1 else 0)  (mod p)`.

For squarefree `N` this gives the exact criterion

`p ∣ F(N, k) ↔ ¬ (p - 1) ∣ k`,

hence the exact evaluation of the gcd

`gcd (F(N, k), N) = ∏ { p ∈ N.primeFactors | ¬ (p - 1) ∣ k }`,

which for a semiprime `N = p q` specialises to
`gcd (F(N, k), N) = (if (p-1) ∣ k then 1 else p) * (if (q-1) ∣ k then 1 else q)`,
and in particular `gcd (F(N, p-1), N) = q` whenever `(q-1) ∤ (p-1)`.

Main results:

* `sum_pow_zmod` — `∑_{x : ZMod p} x ^ k = if (p-1) ∣ k then -1 else 0` for `k ≠ 0`.
* `cast_powerSum` — the local formula for `F(N,k)` modulo a prime divisor of `N`.
* `prime_dvd_powerSum_iff` — `p ∣ F(N,k) ↔ ¬ (p-1) ∣ k` for squarefree `N`.
* `gcd_powerSum_semiprime` — Theorem 1, in exact (all `k`) form.
* `powerSum_reveal` — the factoring corollary at `k = p - 1`.
* `gcd_powerSum_squarefree` — the general squarefree product formula.
* `gcd_powerSum_eq_one_iff` — the gcd is `1` exactly on multiples of the
  Carmichael function `λ(N) = lcm_{p ∣ N} (p-1)`.
-/

open PowerSumReveal

open Finset

/-! ## The local sum over `ZMod p` -/





/-! ## The power sum and its local values -/




/-- In a squarefree modulus a prime divisor does not divide the complementary cofactor. -/
theorem not_dvd_div_of_squarefree {N p : ℕ} (hsq : Squarefree N) (hpN : p ∣ N) (hp : p.Prime) :
    ¬ p ∣ N / p := by
  intro h
  have hNp : N = (N / p) * p := (Nat.div_mul_cancel hpN).symm
  obtain ⟨c, hc⟩ := h
  have : p * p ∣ N := ⟨c, by rw [hNp, hc]; ring⟩
  exact hp.not_isUnit (hsq p this)

/-- **Exact local criterion.**  For squarefree `N`, a prime divisor `p` of `N` divides
`F(N,k)` precisely when `(p-1) ∤ k`. -/
theorem prime_dvd_powerSum_iff {N p k : ℕ} (hp : p.Prime) (hpN : p ∣ N) (hsq : Squarefree N)
    (hk : k ≠ 0) : p ∣ powerSum N k ↔ ¬ (p - 1) ∣ k := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [← ZMod.natCast_eq_zero_iff (powerSum N k) p, cast_powerSum N p k hp hpN hk]
  by_cases hd : (p - 1) ∣ k
  · simp only [hd, if_true, not_true_eq_false, iff_false]
    intro h
    have h' : ((N / p : ℕ) : ZMod p) = 0 := by
      rw [nsmul_eq_mul] at h
      simpa using h
    exact not_dvd_div_of_squarefree hsq hpN hp ((ZMod.natCast_eq_zero_iff _ p).mp h')
  · simp [hd]

/-! ## The gcd evaluation -/






/-! ## The general squarefree formula -/





open PowerSumReveal in
theorem solution{N k : ℕ} (hN : N ≠ 0) (hsq : Squarefree N) (hk : k ≠ 0) :
    Nat.gcd (powerSum N k) N = ∏ p ∈ N.primeFactors.filter (fun p => ¬ (p - 1) ∣ k), p := by
  classical
  set S : Finset ℕ := N.primeFactors.filter (fun p => ¬ (p - 1) ∣ k) with hS
  refine Nat.dvd_antisymm ?_ ?_
  · -- gcd divides the product: the gcd is squarefree and all its prime factors lie in `S`
    have hgN : Nat.gcd (powerSum N k) N ∣ N := Nat.gcd_dvd_right _ _
    have hgsq : Squarefree (Nat.gcd (powerSum N k) N) := hsq.squarefree_of_dvd hgN
    have hg0 : Nat.gcd (powerSum N k) N ≠ 0 := by
      intro h
      exact hN (Nat.eq_zero_of_gcd_eq_zero_right h)
    have hprod : ∏ p ∈ (Nat.gcd (powerSum N k) N).primeFactors, p = Nat.gcd (powerSum N k) N :=
      Nat.prod_primeFactors_of_squarefree hgsq
    rw [← hprod]
    refine Finset.prod_dvd_prod_of_subset _ _ _ ?_
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpg : p ∣ Nat.gcd (powerSum N k) N := Nat.dvd_of_mem_primeFactors hp
    have hpN : p ∣ N := hpg.trans hgN
    have hpF : p ∣ powerSum N k := hpg.trans (Nat.gcd_dvd_left _ _)
    have : ¬ (p - 1) ∣ k := (prime_dvd_powerSum_iff hpp hpN hsq hk).mp hpF
    simp [hS, Nat.mem_primeFactors, hpp, hpN, hN, this]
  · -- the product divides the gcd
    have hSN : ∀ p ∈ S, p.Prime ∧ p ∣ N ∧ p ∣ powerSum N k := by
      intro p hp
      rw [hS, Finset.mem_filter, Nat.mem_primeFactors] at hp
      obtain ⟨⟨hpp, hpN, _⟩, hk'⟩ := hp
      exact ⟨hpp, hpN, (prime_dvd_powerSum_iff hpp hpN hsq hk).mpr hk'⟩
    have hdvdN : (∏ p ∈ S, p) ∣ N := by
      refine Finset.prod_primes_dvd _ ?_ ?_
      · intro p hp; exact (hSN p hp).1.prime
      · intro p hp; exact (hSN p hp).2.1
    have hdvdF : (∏ p ∈ S, p) ∣ powerSum N k := by
      refine Finset.prod_primes_dvd _ ?_ ?_
      · intro p hp; exact (hSN p hp).1.prime
      · intro p hp; exact (hSN p hp).2.2
    exact Nat.dvd_gcd hdvdF hdvdN
