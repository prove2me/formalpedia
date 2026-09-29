-- Prove2me | Theorems.Thm_PowerSumGCD_gcd_powerSum_gcd_eq_lcm
-- name    : PowerSumGCD.gcd_powerSum_gcd_eq_lcm
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:22:26.686251+00:00
-- url     : https://prove2.me/theorems/59559167-b696-44d4-9cfb-7513bc11080b
-- title:
--   The anti-homomorphism law.
-- statement:
--   **The anti-homomorphism law.**  For squarefree `N` and positive exponents,
--   `g_N(gcd(k,k')) = lcm(g_N(k), g_N(k'))`.
--
--   ```lean
--   theorem PowerSumGCD.gcd_powerSum_gcd_eq_lcm{N k k' : ℕ} (hN : Squarefree N) (hk : 0 < k) (hk' : 0 < k') :
--       Nat.gcd (powerSum N (Nat.gcd k k')) N
--         = Nat.lcm (Nat.gcd (powerSum N k) N) (Nat.gcd (powerSum N k') N) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/PowerSumGCDLattice.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/PowerSumGCDLattice.lean#L43

-- Thm stub generated from Novelty/PowerSumGCDLattice.lean
import Mathlib
import Definitions.Def_Novelty_PowerSumGCDFactoring
import Definitions.Def_Novelty_PowerSumGCDGeneral

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

theorem PowerSumGCD.gcd_powerSum_gcd_eq_lcm{N k k' : ℕ} (hN : Squarefree N) (hk : 0 < k) (hk' : 0 < k') :
    Nat.gcd (powerSum N (Nat.gcd k k')) N
      = Nat.lcm (Nat.gcd (powerSum N k) N) (Nat.gcd (powerSum N k') N) := by sorry
