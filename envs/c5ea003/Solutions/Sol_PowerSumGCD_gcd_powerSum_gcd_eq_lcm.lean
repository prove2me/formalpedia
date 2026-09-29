-- Prove2me | solution 1 for PowerSumGCD.gcd_powerSum_gcd_eq_lcm
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T03:33:13.371255+00:00
-- url     : https://prove2.me/submissions/1efd7f89-b95d-43fb-bc83-cc61093c006e

-- Sol generated from Novelty/PowerSumGCDLattice.lean
import Mathlib
import Definitions.Def_Novelty_PowerSumGCDFactoring
import Definitions.Def_Novelty_PowerSumGCDGeneral
import Theorems.Thm_PowerSumGCD_gcd_powerSum_squarefree

/-!
# The power-sum gcd is a lattice anti-homomorphism

Write `g_N(k) = gcd(F(N,k), N)`.  For squarefree `N` the product formula
`gcd_powerSum_squarefree` says that `g_N(k)` is the product of the primes `r ∣ N` whose
"order condition" `(r-1) ∣ k` **fails**.  Since `(r-1) ∣ gcd(k,k')` iff `(r-1)` divides
both, the failure set of `gcd(k,k')` is the *union* of the two failure sets, and unions of
sets of distinct primes correspond to `lcm`s of their products.  Hence

  `g_N(gcd(k,k')) = lcm(g_N(k), g_N(k'))`,

i.e. `g_N` carries the gcd-lattice of exponents to the lcm-lattice of divisors of `N` —
an order-reversing lattice morphism.  A first corollary is monotonicity: refining the
exponent (`k ∣ k'`) can only shrink the revealed factor.

## Main results

* `prod_union_eq_lcm_prod` : for finsets of primes, `∏ (s ∪ t) = lcm (∏ s) (∏ t)`;
* `gcd_powerSum_gcd_eq_lcm` : the anti-homomorphism law;
* `gcd_powerSum_dvd_of_dvd` : `k ∣ k'` (both positive) implies `g_N(k') ∣ g_N(k)`;
* `gcd_powerSum_gcd_eq_one` : the trivial locus of `g_N` is closed under `gcd`;
* `gcd_powerSum_pairwise_lcm_eq_self` : if `g_N(gcd(k,k')) = N` then
  `lcm(g_N(k), g_N(k')) = N`.
-/

open Finset

open PowerSumGCD

/-- The product over a union of finsets of primes is the `lcm` of the two products. -/
theorem prod_union_eq_lcm_prod {s t : Finset ℕ} (hprime : ∀ r ∈ s ∪ t, r.Prime) :
    ∏ r ∈ s ∪ t, r = Nat.lcm (∏ r ∈ s, r) (∏ r ∈ t, r) := by
  classical
  refine Nat.dvd_antisymm ?_ ?_
  · refine Finset.prod_primes_dvd _ (fun a ha => (hprime a ha).prime) fun a ha => ?_
    rcases Finset.mem_union.mp ha with h | h
    · exact dvd_trans (Finset.dvd_prod_of_mem _ h) (Nat.dvd_lcm_left _ _)
    · exact dvd_trans (Finset.dvd_prod_of_mem _ h) (Nat.dvd_lcm_right _ _)
  · exact Nat.lcm_dvd (Finset.prod_dvd_prod_of_subset _ _ _ Finset.subset_union_left)
      (Finset.prod_dvd_prod_of_subset _ _ _ Finset.subset_union_right)






open PowerSumGCD in
theorem solution{N k k' : ℕ} (hN : Squarefree N) (hk : 0 < k) (hk' : 0 < k') :
    Nat.gcd (powerSum N (Nat.gcd k k')) N
      = Nat.lcm (Nat.gcd (powerSum N k) N) (Nat.gcd (powerSum N k') N) := by
  classical
  have hg : 0 < Nat.gcd k k' := Nat.gcd_pos_of_pos_left _ hk
  rw [gcd_powerSum_squarefree hN hg, gcd_powerSum_squarefree hN hk,
    gcd_powerSum_squarefree hN hk']
  have hfil : N.primeFactors.filter (fun r => ¬ (r - 1) ∣ Nat.gcd k k')
      = N.primeFactors.filter (fun r => ¬ (r - 1) ∣ k)
        ∪ N.primeFactors.filter (fun r => ¬ (r - 1) ∣ k') := by
    rw [← Finset.filter_or]
    refine Finset.filter_congr fun r _ => ?_
    constructor
    · intro h
      by_contra hcon
      push_neg at hcon
      exact h (Nat.dvd_gcd hcon.1 hcon.2)
    · rintro (h | h) hcon
      · exact h (hcon.trans (Nat.gcd_dvd_left k k'))
      · exact h (hcon.trans (Nat.gcd_dvd_right k k'))
  rw [hfil]
  refine prod_union_eq_lcm_prod fun r hr => ?_
  rcases Finset.mem_union.mp hr with h | h <;>
    exact Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp h).1
