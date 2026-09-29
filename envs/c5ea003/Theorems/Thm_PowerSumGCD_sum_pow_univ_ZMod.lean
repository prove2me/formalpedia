-- Prove2me | Theorems.Thm_PowerSumGCD_sum_pow_univ_ZMod
-- name    : PowerSumGCD.sum_pow_univ_ZMod
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:20:36.496462+00:00
-- url     : https://prove2.me/theorems/a7d1958b-0d51-468c-8ae4-522242b4e323
-- title:
--   Complete power sum over a prime field.
-- statement:
--   **Complete power sum over a prime field.**  For `k > 0`,
--   `∑_{x ∈ ZMod p} x^k = -1` if `(p-1) ∣ k` and `0` otherwise.
--
--   ```lean
--   theorem PowerSumGCD.sum_pow_univ_ZMod(p : ℕ) [Fact p.Prime] {k : ℕ} (hk : 0 < k) :
--       ∑ x : ZMod p, x ^ k = if (p - 1) ∣ k then -1 else 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/PowerSumGCDFactoring.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/PowerSumGCDFactoring.lean#L85

-- Thm stub generated from Novelty/PowerSumGCDFactoring.lean
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

theorem PowerSumGCD.sum_pow_univ_ZMod(p : ℕ) [Fact p.Prime] {k : ℕ} (hk : 0 < k) :
    ∑ x : ZMod p, x ^ k = if (p - 1) ∣ k then -1 else 0 := by sorry
