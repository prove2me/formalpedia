-- Prove2me | solution 1 for PowerSumGCD.sum_pow_univ_ZMod
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T03:23:46.306284+00:00
-- url     : https://prove2.me/submissions/52e5ef85-8be6-46db-a32e-19cafd133005

-- Sol generated from Novelty/PowerSumGCDFactoring.lean
import Mathlib
import Definitions.Def_Novelty_PowerSumGCDFactoring

/-!
# Power-sum GCD factoring: `gcd(∑_{a=1}^{N} a^k, N)` reveals the prime factors

Let `F(N,k) = ∑_{a=1}^{N} a^k` (`powerSum N k` below).  For a prime `r` dividing
`N` exactly once, the residues `1, …, N` cover each residue class mod `r` the
same number of times, so mod `r` the power sum collapses to a multiple of the
complete power sum `∑_{x : ZMod r} x^k`, which is the classical `-1`/`0`
dichotomy of finite fields.  The upshot is a *complete* characterisation

  `r ∣ F(N,k)  ↔  ¬ (r-1) ∣ k`      (`prime_dvd_powerSum_iff`)

from which the whole "factor reveal" phenomenon follows by elementary gcd
bookkeeping.

## Main results

* `sum_pow_univ_ZMod` : `∑ x : ZMod p, x^k = if (p-1) ∣ k then -1 else 0` for
  `k > 0` (the complete-power-sum dichotomy, including the zero element).
* `cast_powerSum` : `(F(p*q, k) : ZMod p) = q * (if (p-1) ∣ k then -1 else 0)`.
* `prime_dvd_powerSum_iff` : the divisibility characterisation above.
* `gcd_powerSum_semiprime` : for distinct primes `p q` and `k > 0`,
  `gcd (F(pq,k)) (pq) = (if (p-1) ∣ k then 1 else p) * (if (q-1) ∣ k then 1 else q)`.
* `gcd_powerSum_eq_factor` : **Theorem 1** — if `(q-1) ∤ (p-1)` then
  `gcd (F(pq, p-1)) (pq) = q`, a nontrivial factor of `N = pq`.
* `powerSum_coprime_iff_squarefree` : for squarefree `N`, `F(N,k)` is coprime to
  `N` exactly when every prime `r ∣ N` satisfies `(r-1) ∣ k` — the Carmichael
  condition.
-/

open Finset

open PowerSumGCD






variable {R : Type*} [AddCommMonoid R]














open PowerSumGCD in
theorem solution(p : ℕ) [Fact p.Prime] {k : ℕ} (hk : 0 < k) :
    ∑ x : ZMod p, x ^ k = if (p - 1) ∣ k then -1 else 0 := by
  classical
  have h0 : ∑ x : ZMod p, x ^ k = ∑ x ∈ (univ : Finset (ZMod p)) \ {0}, x ^ k := by
    rw [← Finset.sum_sdiff ({0} : Finset (ZMod p)).subset_univ, Finset.sum_singleton,
      zero_pow hk.ne', add_zero]
  have h1 : ∑ x ∈ (univ : Finset (ZMod p)) \ {0}, x ^ k = ∑ x : (ZMod p)ˣ, (x ^ k : ZMod p) := by
    let φ : (ZMod p)ˣ ↪ ZMod p := ⟨fun x ↦ x, Units.val_injective⟩
    have hmap : univ.map φ = univ \ {0} := by
      ext x
      simpa only [Finset.mem_map, Finset.mem_univ, Function.Embedding.coeFn_mk, true_and,
        Finset.mem_sdiff, Finset.mem_singleton, φ] using isUnit_iff_ne_zero
    simp [φ, ← hmap, univ.sum_map φ]
  rw [h0, h1, FiniteField.sum_pow_units (ZMod p) k]
  simp [ZMod.card]
