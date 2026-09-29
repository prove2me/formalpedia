-- Prove2me | solution 1 for PowerSumGCD.cast_powerSum
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T03:25:29.726266+00:00
-- url     : https://prove2.me/submissions/5133b786-32c3-43d8-81e3-faec64d658ea

-- Sol generated from Novelty/PowerSumGCDFactoring.lean
import Mathlib
import Definitions.Def_Novelty_PowerSumGCDFactoring
import Theorems.Thm_PowerSumGCD_sum_pow_univ_ZMod
import Theorems.Thm_PowerSumGCD_sum_range_mul_cast

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



lemma powerSum_succ (N k : ℕ) : powerSum (N + 1) k = powerSum N k + (N + 1) ^ k := by
  simp [powerSum, Finset.sum_Icc_succ_top (Nat.succ_le_succ (Nat.zero_le N))]

/-- For `k > 0` the power sum over `1, …, N` is the sum over `range N` plus the top term
(the `a = 0` term vanishes). -/
lemma powerSum_eq_sum_range_add (N k : ℕ) (hk : 0 < k) :
    powerSum N k = (∑ a ∈ Finset.range N, a ^ k) + N ^ k := by
  induction N with
  | zero => simp [powerSum, zero_pow hk.ne']
  | succ N ih => rw [powerSum_succ, ih, Finset.sum_range_succ]


variable {R : Type*} [AddCommMonoid R]














open PowerSumGCD in
theorem solution(p q : ℕ) [Fact p.Prime] {k : ℕ} (hk : 0 < k) :
    ((powerSum (p * q) k : ℕ) : ZMod p) = (q : ZMod p) * (if (p - 1) ∣ k then -1 else 0) := by
  have hp : p ≠ 0 := (Fact.out (p := p.Prime)).pos.ne'
  haveI : NeZero p := ⟨hp⟩
  rw [powerSum_eq_sum_range_add _ _ hk]
  push_cast
  have h1 : ((p : ZMod p) * (q : ZMod p)) ^ k = 0 := by
    simp [zero_pow hk.ne']
  have h2 : ∑ a ∈ Finset.range (p * q), ((a : ZMod p)) ^ k = q • ∑ x : ZMod p, x ^ k :=
    sum_range_mul_cast p (fun x => x ^ k) q
  rw [h1, add_zero, h2, sum_pow_univ_ZMod p hk, nsmul_eq_mul]
