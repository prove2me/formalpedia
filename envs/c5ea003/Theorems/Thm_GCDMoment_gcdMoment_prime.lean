-- Prove2me | Theorems.Thm_GCDMoment_gcdMoment_prime
-- name    : GCDMoment.gcdMoment_prime
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:51:22.616556+00:00
-- url     : https://prove2.me/theorems/51ab1cef-a80c-49a9-869b-f568f8b79c43
-- title:
--   The local factor at a prime: `M_k(p) = p^k + p − 1`.
-- statement:
--   **The local factor at a prime**: `M_k(p) = p^k + p − 1`.
--
--   ```lean
--   theorem GCDMoment.gcdMoment_prime{p : ℕ} (hp : p.Prime) (k : ℕ) : gcdMoment k p = p ^ k + p - 1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/GCDMomentMultiplicative.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/GCDMomentMultiplicative.lean#L94

-- Thm stub generated from Novelty/GCDMomentMultiplicative.lean
import Mathlib
import Definitions.Def_Novelty_GCDMomentMultiplicative
import Definitions.Def_Novelty_GCDMomentPairInversion
import Definitions.Def_Novelty_GCDMomentTraceWitness

/-!
# The gcd moments are a multiplicative family: beyond semiprimes

`Novelty.GCDMomentTraceWitness` computes `M_k(N) = ∑_{x < N} gcd(N,x)^k` for a *semiprime*
`N = pq` and reads off the trace-witness structure.  This file removes the semiprime
restriction: `M_k` is the Dirichlet convolution `(n ↦ n^k) * φ`, hence multiplicative, so its
value at an arbitrary modulus is a product over the prime-power part of the factorisation.

The consequence for the trace-witness picture is sharp.  For a *squarefree* modulus

`M_k(n) = ∏_{p ∣ n} (p^k + p − 1)`,

so the moment is an Euler product over the prime factors: it is not just a symmetric function
of the factors, it is a **completely split** one, with one local factor per prime.  Specialising
to `n = pq` reproduces the semiprime four-term formula, and shows that the four terms of the
closed form are nothing but the expansion of a two-factor Euler product.

## Main results

* `gcdMomentAF` — the gcd moment as an arithmetic function, `pow k * phiAF`.
* `gcdMomentAF_isMultiplicative` — multiplicativity.
* `gcdMomentAF_apply_eq` — the arithmetic function agrees with `gcdMoment` on `n > 0`.
* `gcdMoment_mul_of_coprime` — `M_k(mn) = M_k(m) M_k(n)` for coprime `m, n > 0`.
* `gcdMoment_prime` — the local factor `M_k(p) = p^k + p − 1`.
* `gcdMoment_prime_pow`, `gcdMoment_prime_pow_closed` — the local factor at a prime power,
  `∑_{i ≤ e} p^{ik} φ(p^{e−i}) = p^{ek} + (p−1)∑_{i<e} p^{ik} p^{e−1−i}`.
* `gcdMoment_squarefree` — **the Euler product** `M_k(n) = ∏_{p ∣ n} (p^k + p − 1)`.
* `gcdMoment_ge_local`, `gcdMoment_gt_local_of_not_prime`, `gcdMoment_eq_local_iff_prime` —
  **the moment detects primality**: `M_k(n) ≥ n^k + n − 1` always, with equality iff `n` is
  prime.
* `gcdMoment_semiprime_euler` — the semiprime case as a two-factor product, and
  `gcdMoment_semiprime_euler_eq_four_terms` — its agreement with the closed form of the
  companion file.
* `gcdMoment_factorization` — the general modulus: a product over the prime factorisation.
* `pairMoment_eq_euler` — the predicted moment of a *candidate* factorisation is the same
  two-factor Euler product, which is what makes the inversion analysis of the companion files
  a statement about local factors.
* `euler_local_factor_refine`, `pairMoment_gt_trivial` — the local factor `t ↦ t^k + t − 1` is
  strictly submultiplicative on `t ≥ 2`: refining a factorisation strictly raises the moment.
* `eulerProd_ge_eulerLocal`, `eulerProd_gt_eulerLocal` — the same for an arbitrary number of
  factors: any splitting into `r ≥ 2` parts strictly raises the predicted moment.
-/

open GCDMoment

open Finset ArithmeticFunction

theorem GCDMoment.gcdMoment_prime{p : ℕ} (hp : p.Prime) (k : ℕ) : gcdMoment k p = p ^ k + p - 1 := by sorry
