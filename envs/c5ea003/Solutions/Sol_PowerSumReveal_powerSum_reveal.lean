-- Prove2me | solution 1 for PowerSumReveal.powerSum_reveal
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T00:13:45.046065+00:00
-- url     : https://prove2.me/submissions/f6359a3f-291a-4491-9fda-65be1dd78057

-- Sol generated from Combinatorics/PowerSumFactorReveal.lean
import Mathlib
import Definitions.Def_Combinatorics_PowerSumFactorReveal
import Theorems.Thm_PowerSumReveal_cast_powerSum
import Theorems.Thm_PowerSumReveal_gcd_two_primes

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


/-- A semiprime is squarefree. -/
theorem squarefree_semiprime {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    Squarefree (p * q) :=
  Nat.squarefree_mul_iff.mpr ⟨(Nat.coprime_primes hp hq).mpr hpq, hp.squarefree, hq.squarefree⟩

/-- **Theorem 1 (power-sum factor reveal), exact form.**  For a semiprime `N = p q` and any
exponent `k ≥ 1`,
`gcd (F(N,k), N) = (if (p-1) ∣ k then 1 else p) * (if (q-1) ∣ k then 1 else q)`. -/
theorem gcd_powerSum_semiprime {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {k : ℕ}
    (hk : k ≠ 0) :
    Nat.gcd (powerSum (p * q) k) (p * q)
      = (if (p - 1) ∣ k then 1 else p) * (if (q - 1) ∣ k then 1 else q) := by
  have hsq := squarefree_semiprime hp hq hpq
  have hpdvd : p ∣ powerSum (p * q) k ↔ ¬ (p - 1) ∣ k :=
    prime_dvd_powerSum_iff hp ⟨q, rfl⟩ hsq hk
  have hqdvd : q ∣ powerSum (p * q) k ↔ ¬ (q - 1) ∣ k :=
    prime_dvd_powerSum_iff hq ⟨p, mul_comm p q⟩ hsq hk
  rw [gcd_two_primes hp hq hpq]
  by_cases h1 : (p - 1) ∣ k <;> by_cases h2 : (q - 1) ∣ k <;>
    simp [h1, h2, hpdvd, hqdvd]



/-! ## The general squarefree formula -/





open PowerSumReveal in
theorem solution{p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hdvd : ¬ (q - 1) ∣ (p - 1)) :
    Nat.gcd (powerSum (p * q) (p - 1)) (p * q) = q := by
  have hk : p - 1 ≠ 0 := by
    have := hp.two_le; omega
  rw [gcd_powerSum_semiprime hp hq hpq hk]
  simp [hdvd]
