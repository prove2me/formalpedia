-- Prove2me | solution 1 for PowerSumGCD.sum_range_mul_cast
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T03:23:46.834923+00:00
-- url     : https://prove2.me/submissions/33725e54-a1d1-4295-bec1-3d48c5a726ce

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

/-- Summing `f` over the canonical representatives `0, …, p-1` is summing over `ZMod p`. -/
lemma sum_range_cast (p : ℕ) [NeZero p] (f : ZMod p → R) :
    ∑ r ∈ Finset.range p, f (r : ZMod p) = ∑ x : ZMod p, f x := by
  refine Finset.sum_nbij (fun r => ((r : ℕ) : ZMod p)) ?_ ?_ ?_ ?_
  · intros; exact Finset.mem_univ _
  · intro a ha b hb hab
    simp only [Finset.mem_coe, Finset.mem_range] at ha hb
    have := congrArg ZMod.val hab
    rwa [ZMod.val_natCast_of_lt ha, ZMod.val_natCast_of_lt hb] at this
  · intro x _
    exact ⟨x.val, by simp [ZMod.val_lt], by simp [ZMod.natCast_val]⟩
  · intros; rfl













open PowerSumGCD in
theorem solution(p : ℕ) [NeZero p] (f : ZMod p → R) (n : ℕ) :
    ∑ a ∈ Finset.range (p * n), f (a : ZMod p) = n • ∑ x : ZMod p, f x := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h : p * (n + 1) = p * n + p := by ring
    rw [h, Finset.sum_range_add, ih, succ_nsmul]
    congr 1
    rw [← sum_range_cast p f]
    refine Finset.sum_congr rfl fun r _ => ?_
    congr 1
    push_cast
    simp
