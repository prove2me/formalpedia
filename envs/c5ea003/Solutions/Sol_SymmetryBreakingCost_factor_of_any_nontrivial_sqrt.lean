-- Prove2me | solution 1 for SymmetryBreakingCost.factor_of_any_nontrivial_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T06:05:11.791059+00:00
-- url     : https://prove2.me/submissions/f3955355-6b3c-4b4c-87af-5e855f85bd7d

-- Sol generated from Novelty/SymmetryBreakingCostWitness.lean
import Mathlib
import Definitions.Def_Novelty_SymmetryBreakingCostKernel
import Theorems.Thm_SymmetryBreakingCost_gcd_eq_prime_of_dvd

/-!
# The witness always exists: information present, search sealed

Cycles 1–3 measured the two classical resources.  This fourth cycle closes the loop on the
*asymmetric* side by showing that the object Shor's algorithm hunts for is never missing:

* `exists_nontrivial_sqrt_one` : every odd semiprime `N = p q` admits an explicit `x` with
  `x² ≡ 1 (mod N)` and `x ≢ ±1 (mod N)` — built by the Chinese remainder theorem, exactly the
  same freedom that makes the residue oracle cheap.
* `gcd_witness_eq_prime` : for that witness, `gcd(x - 1, N) = p` **on the nose**; one gcd
  recovers the factor.
* `factor_of_any_nontrivial_sqrt` : conversely *every* nontrivial square root of `1` mod `N`
  factors `N` — `gcd(z - 1, N)` is `p` or `q`, there is no third kind of witness.
* `symmetry_breaking_cost_table` : the three measurements side by side for an odd semiprime —
  the oracle cost is exactly `⌈log₂ |S|⌉`, the public battery excludes no candidate at all, and
  an asymmetric witness that factors `N` in one gcd exists.

The moral of the measurement: for every odd semiprime, factoring data is *present* in the
arithmetic (a residue signature isolating `p₀` in `⌈log₂ |S|⌉` bits, a square root of unity
revealing `p` in one gcd).  What is missing is a symmetry-breaking *resource* that points at it;
the classical public data `[(a | N)]` is provably blind (cycle 2), and this is what the quantum
order-finding channel buys.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer, cycle 4): the nontrivial square roots of unity are never rare or
absent — the obstruction is purely search, never existence.

Experiment (Experimenter): for `(p, q) = (3,5), (3,7), (3,11), (5,7), (7,11), (11,13)` the CRT
witness `x ≡ 1 mod p`, `x ≡ -1 mod q` is `x = 4, 13, 10, 6, 43, 12`; in every case `x² ≡ 1 mod
N` and `gcd(x - 1, N) = p`, i.e. `3, 3, 3, 5, 7, 11`, confirming the two theorems below on
concrete inputs.

Analysis (Analyst): the construction and the oracle construction of cycle 1 are the *same*
mechanism — prescribing independent local data and gluing by CRT.  What differs is whether the
prescribed data is readable from `N`: the local Legendre symbols and the local square roots are
both invisible to the symmetric battery, by the kernel theorem of cycle 2.

Critique (Critic): `gcd_witness_eq_prime` must not be vacuous, so the witness is produced
explicitly rather than assumed, and the hypotheses are only `p ≠ q` odd primes; the numerical
run above checks the statement on six semiprimes.
-/

open SymmetryBreakingCost

open Finset
open scoped NumberTheorySymbols





/-! ## Cycle 5.  Every nontrivial square root factors, and there is no third kind -/



open SymmetryBreakingCost in
theorem solution{p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hp2 : p ≠ 2)
    (hq2 : q ≠ 2) (hpq : p ≠ q) {z : ℤ} (hz : ((p * q : ℕ) : ℤ) ∣ z ^ 2 - 1)
    (h1 : ¬((p * q : ℕ) : ℤ) ∣ z - 1) (h2 : ¬((p * q : ℕ) : ℤ) ∣ z + 1) :
    Int.gcd (z - 1) ((p * q : ℕ) : ℤ) = p ∨ Int.gcd (z - 1) ((p * q : ℕ) : ℤ) = q := by
  have hcast : ((p * q : ℕ) : ℤ) = (p : ℤ) * (q : ℤ) := by push_cast; ring
  have hfac : (z - 1) * (z + 1) = z ^ 2 - 1 := by ring
  have hpprime : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hqprime : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
  have hcopZ : IsCoprime ((p : ℤ)) ((q : ℤ)) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    simpa [Int.gcd_natCast_natCast] using (Nat.coprime_primes hp hq).mpr hpq
  have hpz : (p : ℤ) ∣ (z - 1) * (z + 1) := by
    rw [hfac]
    exact dvd_trans (by rw [hcast]; exact Dvd.intro (q : ℤ) rfl) hz
  have hqz : (q : ℤ) ∣ (z - 1) * (z + 1) := by
    rw [hfac]
    exact dvd_trans (by rw [hcast]; exact Dvd.intro_left (p : ℤ) rfl) hz
  have hnot2p : ¬((p : ℤ) ∣ 2) := by
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (by exact_mod_cast h))
  have hnot2q : ¬((q : ℤ) ∣ 2) := by
    intro h
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (by exact_mod_cast h))
  rcases hpprime.dvd_mul.mp hpz with hpm | hpp <;> rcases hqprime.dvd_mul.mp hqz with hqm | hqp
  · exact absurd (by rw [hcast]; exact hcopZ.mul_dvd hpm hqm) h1
  · exact Or.inl (gcd_eq_prime_of_dvd hp hq hpm (fun hc => hnot2q (by simpa using dvd_sub hqp hc)))
  · refine Or.inr ?_
    rw [Nat.mul_comm]
    exact gcd_eq_prime_of_dvd hq hp hqm (fun hc => hnot2p (by simpa using dvd_sub hpp hc))
  · exact absurd (by rw [hcast]; exact hcopZ.mul_dvd hpp hqp) h2
