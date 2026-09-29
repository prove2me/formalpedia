-- Prove2me | solution 1 for PowerSumGCD.gcd_powerSum_eq_factor
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T03:31:46.571807+00:00
-- url     : https://prove2.me/submissions/1ec39d73-c62a-4a29-9999-321782b55f37

-- Sol generated from Novelty/PowerSumGCDFactoring.lean
import Mathlib
import Definitions.Def_Novelty_PowerSumGCDFactoring
import Theorems.Thm_PowerSumGCD_gcd_powerSum_semiprime

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
theorem solution{p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hdvd : ¬ (q - 1) ∣ (p - 1)) :
    Nat.gcd (powerSum (p * q) (p - 1)) (p * q) = q := by
  have hk : 0 < p - 1 := by
    have := hp.two_le; omega
  rw [gcd_powerSum_semiprime hp hq hpq hk, if_pos dvd_rfl, if_neg hdvd, one_mul]
