-- Prove2me | solution 1 for SymmetryBreakingCost.exists_nontrivial_sqrt_one
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T06:01:20.24242+00:00
-- url     : https://prove2.me/submissions/0b2eb4fd-be41-4796-ab1e-8bf8bacc3ee5

-- Sol generated from Novelty/SymmetryBreakingCostWitness.lean
import Mathlib
import Definitions.Def_Novelty_SymmetryBreakingCostKernel
import Theorems.Thm_SymmetryBreakingCost_crt_finset

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
    (hq2 : q ≠ 2) (hpq : p ≠ q) :
    ∃ x : ℤ, (p : ℤ) ∣ x - 1 ∧ (q : ℤ) ∣ x + 1 ∧
      ((p * q : ℕ) : ℤ) ∣ x ^ 2 - 1 ∧ ¬((p * q : ℕ) : ℤ) ∣ x - 1 ∧ ¬((p * q : ℕ) : ℤ) ∣ x + 1 := by
  classical
  have hcop : (({p, q} : Finset ℕ) : Set ℕ).Pairwise Nat.Coprime := by
    intro x hx y hy hxy
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
      first
        | exact absurd rfl hxy
        | exact (Nat.coprime_primes hp hq).mpr hpq
        | exact (Nat.coprime_primes hq hp).mpr (Ne.symm hpq)
  obtain ⟨x, hx⟩ := crt_finset {p, q} hcop (fun r => if r = p then 1 else -1)
  have hxp : (p : ℤ) ∣ x - 1 := by simpa using hx p (by simp)
  have hxq : (q : ℤ) ∣ x + 1 := by
    have := hx q (by simp)
    rw [if_neg (Ne.symm hpq)] at this
    simpa [sub_neg_eq_add] using this
  have hp2' : ¬((p : ℤ) ∣ 2) := by
    intro h
    have : p ∣ 2 := by exact_mod_cast h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
  have hq2' : ¬((q : ℤ) ∣ 2) := by
    intro h
    have : q ∣ 2 := by exact_mod_cast h
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp this)
  refine ⟨x, hxp, hxq, ?_, ?_, ?_⟩
  · have : ((p * q : ℕ) : ℤ) = (p : ℤ) * (q : ℤ) := by push_cast; ring
    rw [this, show x ^ 2 - 1 = (x - 1) * (x + 1) by ring]
    exact mul_dvd_mul hxp hxq
  · intro hdvd
    have hqd : (q : ℤ) ∣ x - 1 := dvd_trans ⟨(p : ℤ), by push_cast; ring⟩ hdvd
    exact hq2' (by simpa using dvd_sub hxq hqd)
  · intro hdvd
    have hpd : (p : ℤ) ∣ x + 1 := dvd_trans ⟨(q : ℤ), by push_cast; ring⟩ hdvd
    exact hp2' (by simpa using dvd_sub hpd hxp)
