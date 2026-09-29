-- Prove2me | solution 1 for GCDMoment.gcdMoment_le_primeProd
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T00:15:31.764123+00:00
-- url     : https://prove2.me/submissions/275a0761-a0a4-4edb-afa8-170aa416aceb

-- Sol generated from Novelty/GCDMomentRefinementOrder.lean
import Mathlib
import Definitions.Def_Novelty_GCDMomentMultiplicative
import Definitions.Def_Novelty_GCDMomentPairInversion
import Definitions.Def_Novelty_GCDMomentRefinementOrder
import Definitions.Def_Novelty_GCDMomentTraceWitness
import Theorems.Thm_GCDMoment_gcdMoment_mul_of_coprime
import Theorems.Thm_GCDMoment_gcdMoment_prime_pow_le
import Theorems.Thm_GCDMoment_primeProd_mul
import Theorems.Thm_GCDMoment_primeProd_one

/-!
# The refinement order on gcd moments: the prime factorisation is the maximum

This file is the third cycle of the gcd-moment project
(`Novelty.GCDMomentTraceWitness`, `Novelty.GCDMomentPairInversion`,
`Novelty.GCDMomentMultiplicative`).  The previous cycle proved the *bottom* of the refinement
order: the moment of a modulus is at least its own local Euler factor
(`gcdMoment_ge_local`), with equality exactly at the primes, and splitting a factor strictly
raises the *predicted* Euler product (`eulerProd_gt_eulerLocal`).

Here we prove the *top* of that order.  Write

`Π_k(n) = ∏_{p ∈ primeFactorsList n} (p^k + p − 1)`

for the Euler product read off the full prime factorisation counted with multiplicity
(`primeProd`, the finest possible factorisation of `n`).  Then:

## Main results

* `gcdMoment_prime_pow_succ` — the local recursion `M_k(p^{e+1}) = p^k M_k(p^e) + φ(p^{e+1})`,
  which drives every estimate below.
* `gcdMoment_prime_pow_le`, `gcdMoment_prime_pow_lt` — `M_k(p^e) ≤ (p^k+p−1)^e`, strictly as
  soon as `e ≥ 2`: a prime power is *cheaper* than the same number of independent primes.
* `gcdMoment_prime_sq_deficiency`, `gcdMoment_prime_pow_deficiency` — the exact gap at a
  square, `(p^k+p−1)^2 − M_k(p^2) = (p−1)(p^k−1)`, and its closed form at every prime power.
* `gcdMoment_le_primeProd` — **the upper envelope**: `M_k(n) ≤ Π_k(n)` for every `n > 0`
  and every `k ≥ 1`.
* `gcdMoment_eq_primeProd_iff_squarefree` — **equality holds exactly on the squarefree moduli**.
  Together with `gcdMoment_eq_local_iff_prime` (previous cycle) this brackets the moment
  between two Euler products whose equality cases are precisely "`n` prime" and
  "`n` squarefree": `n^k + n − 1 ≤ M_k(n) ≤ Π_k(n)`.
* `factorisationEuler_le_primeProd` — **the prime factorisation maximises the predicted
  moment**: for *any* factorisation `n = a_1 ⋯ a_r` into parts `≥ 2`, the predicted Euler
  product `∏_i (a_i^k + a_i − 1)` is at most `Π_k(n)`; combined with `eulerProd_ge_eulerLocal`
  the refinement order is now pinned at both ends.
* `primeProd_mul`, `primeProd_prime_pow` — `Π_k` is completely multiplicative, which is what
  makes the induction work and is the exact sense in which the *finest* factorisation is a
  "free" object.

## Lab notes (data behind the statements)

Brute-force values (checked by `decide` at the end of the file):

| `n` | `M_2(n)` | `Π_2(n)` | squarefree? |
|-----|----------|----------|-------------|
| 6   | 55       | 55       | yes |
| 12  | 242      | 275      | no  |
| 4   | 22       | 25       | no  |
| 8   | 92       | 125      | no  |
| 9   | 105      | 121      | no  |

so the gap `Π_k(n) − M_k(n)` is a strictly positive measure of non-squarefreeness, and it is
`0` on the squarefree locus.  The semiprime moduli of the factoring-barrier files are
squarefree, so on them the moment *is* the full Euler product — which is exactly why the
inversion analysis of the previous cycles is possible there and nowhere else.
-/

open GCDMoment

open Finset

/-! ### The local recursion at a prime power -/








/-! ### The Euler product of the finest factorisation -/





theorem primeProd_prime_pow {p : ℕ} (hp : p.Prime) (e k : ℕ) :
    primeProd k (p ^ e) = gcdMoment k p ^ e := by
  simp [primeProd, hp.primeFactorsList_pow]


/-! ### The upper envelope -/





/-! ### The refinement order is pinned at both ends -/






/-! ### Lab notes: brute-force checks of the envelope

`M_2(4) = 22 < 25 = Π_2(4)`, `M_2(8) = 92 < 125`, `M_2(9) = 105 < 121`, while
`M_2(6) = 55 = Π_2(6)` and `M_3(30) = 33669 = Π_3(30)` (squarefree). -/

example : gcdMoment 2 4 = 22 := by decide
example : gcdMoment 2 4 < gcdMoment 2 2 ^ 2 := by decide
example : gcdMoment 2 8 = 92 := by decide
example : gcdMoment 2 8 < gcdMoment 2 2 ^ 3 := by decide
example : gcdMoment 2 9 < gcdMoment 2 3 ^ 2 := by decide
example : gcdMoment 2 6 = gcdMoment 2 2 * gcdMoment 2 3 := by decide
example : gcdMoment 2 12 = gcdMoment 2 4 * gcdMoment 2 3 := by decide
example : gcdMoment 2 9 + (3 - 1) * (3 ^ 2 - 1) = gcdMoment 2 3 ^ 2 := by decide
example : gcdMoment 3 4 + (2 - 1) * (2 ^ 3 - 1) = gcdMoment 3 2 ^ 2 := by decide


open GCDMoment in
theorem solution{k : ℕ} (hk : 1 ≤ k) : ∀ {n : ℕ}, 0 < n →
    gcdMoment k n ≤ primeProd k n := by
  intro n
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p e hp he =>
      intro _
      rw [primeProd_prime_pow hp e]
      exact gcdMoment_prime_pow_le hp hk e
  | zero => intro h; exact absurd h (lt_irrefl 0)
  | one => intro _; simp [gcdMoment]
  | coprime a b ha hb hab iha ihb =>
      intro _
      have ha0 : 0 < a := by omega
      have hb0 : 0 < b := by omega
      rw [gcdMoment_mul_of_coprime ha0 hb0 hab k, primeProd_mul ha0.ne' hb0.ne' k]
      exact Nat.mul_le_mul (iha ha0) (ihb hb0)
