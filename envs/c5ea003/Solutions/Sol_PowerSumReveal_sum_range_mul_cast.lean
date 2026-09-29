-- Prove2me | solution 1 for PowerSumReveal.sum_range_mul_cast
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T00:08:33.61365+00:00
-- url     : https://prove2.me/submissions/fe3d54ed-90d1-435c-84d6-38945d099478

-- Sol generated from Combinatorics/PowerSumFactorReveal.lean
import Mathlib
import Definitions.Def_Combinatorics_PowerSumFactorReveal

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


/-- A block of `p` consecutive naturals starting at `0` hits every residue exactly once:
the general statement, for an arbitrary function on `ZMod p`. -/
theorem sum_range_cast {M : Type*} [AddCommMonoid M] (p : ℕ) [NeZero p] (g : ZMod p → M) :
    ∑ a ∈ range p, g (a : ZMod p) = ∑ x : ZMod p, g x := by
  refine Finset.sum_nbij' (i := fun a => (a : ZMod p)) (j := fun x => x.val) ?_ ?_ ?_ ?_ ?_ <;>
    intros <;> simp_all [ZMod.natCast_val, ZMod.val_lt, Nat.mod_eq_of_lt]



/-! ## The power sum and its local values -/






/-! ## The gcd evaluation -/






/-! ## The general squarefree formula -/





open PowerSumReveal in
theorem solution{M : Type*} [AddCommMonoid M] (p : ℕ) [NeZero p] (g : ZMod p → M)
    (m : ℕ) : ∑ a ∈ range (m * p), g (a : ZMod p) = m • (∑ x : ZMod p, g x) := by
  have hrange : ∀ n : ℕ, ∑ a ∈ range p, g ((n * p + a : ℕ) : ZMod p) = ∑ x : ZMod p, g x := by
    intro n
    rw [← sum_range_cast p g]
    refine Finset.sum_congr rfl ?_
    intro a _
    congr 1
    push_cast [ZMod.natCast_self]
    ring
  induction m with
  | zero => simp
  | succ m ih =>
      have h : (m + 1) * p = m * p + p := by ring
      rw [h, Finset.sum_range_add, ih, hrange, succ_nsmul]
