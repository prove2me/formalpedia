-- Prove2me | Theorems.Thm_GCDMoment_gcdMoment_prime_pow_deficiency
-- name    : GCDMoment.gcdMoment_prime_pow_deficiency
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:56:48.148801+00:00
-- url     : https://prove2.me/theorems/d11a315f-19d8-4f65-a539-c8ef82c447f2
-- title:
--   The exact deficiency at every prime power.
-- statement:
--   **The exact deficiency at every prime power.**  With `L = M_k(p) = p^k + p − 1`,
--
--   `L^e − M_k(p^e) = (p − 1) ∑_{i < e} p^{ik} (L^{e−1−i} − p^{e−1−i})`,
--
--   an explicit finite sum of geometric differences; at `e = 2` it collapses to
--   `(p−1)(p^k−1)` and at `e ≤ 1` to `0`.  This is the quantitative form of
--   `gcdMoment_prime_pow_lt`.
--
--   ```lean
--   theorem GCDMoment.gcdMoment_prime_pow_deficiency{p : ℕ} (hp : p.Prime) (k e : ℕ) :
--       (gcdMoment k p : ℤ) ^ e - (gcdMoment k (p ^ e) : ℤ)
--         = ((p : ℤ) - 1) * ∑ i ∈ Finset.range e, (p : ℤ) ^ (i * k) *
--             ((gcdMoment k p : ℤ) ^ (e - 1 - i) - (p : ℤ) ^ (e - 1 - i)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/GCDMomentRefinementOrder.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/GCDMomentRefinementOrder.lean#L168

-- Thm stub generated from Novelty/GCDMomentRefinementOrder.lean
import Mathlib
import Definitions.Def_Novelty_GCDMomentMultiplicative
import Definitions.Def_Novelty_GCDMomentPairInversion
import Definitions.Def_Novelty_GCDMomentRefinementOrder
import Definitions.Def_Novelty_GCDMomentTraceWitness

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

theorem GCDMoment.gcdMoment_prime_pow_deficiency{p : ℕ} (hp : p.Prime) (k e : ℕ) :
    (gcdMoment k p : ℤ) ^ e - (gcdMoment k (p ^ e) : ℤ)
      = ((p : ℤ) - 1) * ∑ i ∈ Finset.range e, (p : ℤ) ^ (i * k) *
          ((gcdMoment k p : ℤ) ^ (e - 1 - i) - (p : ℤ) ^ (e - 1 - i)) := by sorry
