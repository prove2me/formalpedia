-- Prove2me | Definitions.Def_Novelty_CentralBinomialValuation
-- name    : Novelty_CentralBinomialValuation
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:08:31.378439+00:00
-- url     : https://prove2.me/theorems/69f45553-13f1-4725-aeaa-5a95c34502c5
-- title:
--   Aether Catalog definitions — Novelty_CentralBinomialValuation
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.CentralBinomialValuation`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/CentralBinomialValuation.lean by skeleton subtraction
import Mathlib

/-!
# The `q`-adic valuation of `Aₜ = C(q^{t+1}, qᵗ) − q^{qᵗ}`

Fix a prime base `q`.  The Guedes–Machado construction of composite solutions
`n = qᵗ·p` to `C(qn, n) ≡ qⁿ (mod n)` is driven by the integer
`  Aₜ := C(q^{t+1}, qᵗ) − q^{qᵗ}, `
whose *odd* (prime `≠ q`) divisors `p` supply the second factor of `n`.

This file pins down the exact power of the base `q` itself that divides `Aₜ`.

## Main results

* `central_choose_factorization` : `v_q(C(q^{t+1}, qᵗ)) = 1` for every prime `q`
  and every `t`.  (Kummer/Legendre via
  `Nat.factorization_choose_prime_pow_add_factorization`: exactly one base-`q`
  carry occurs in `qᵗ + (q−1)qᵗ = q^{t+1}`.)
* `A_qadic_valuation` : for a prime `q` and `t ≥ 1`, the base `q` divides `Aₜ`
  exactly once: `q ∣ Aₜ` but `q² ∤ Aₜ`.

The point of `A_qadic_valuation` is structural: because `q ∥ Aₜ`, the base `q`
can never be the prime `p` used in `n = qᵗ·p`, and the "interesting" divisors of
`Aₜ` are precisely the primes `p ≠ q`.  This isolates exactly the search space of
the Guedes–Machado conjecture.

-- !-- Lab Notes -- !--
Hypothesis log / experimental record.

H1 (Hypothesizer). `v_q(C(q^{t+1}, qᵗ)) = 1` for all primes `q` and all `t`.
    EVIDENCE: `#eval ((2^3).choose (2^2)).factorization 2 = 1`,
    `#eval ((3^2).choose (3^1)).factorization 3 = 1`.  CONFIRMED.
    MECHANISM: `v_q(C(q^{t+1}, qᵗ)) + v_q(qᵗ) = t+1` (Kummer prime-power form),
    and `v_q(qᵗ) = t`, so the valuation is `(t+1) − t = 1`.

H2 (Experimenter). Hence `q ∥ Aₜ`.  Indeed `v_q(q^{qᵗ}) = qᵗ ≥ 2` for `t ≥ 1`,
    so `q² ∣ q^{qᵗ}` while `q² ∤ C(q^{t+1}, qᵗ)`; subtracting keeps `q ∣ Aₜ` and
    kills `q² ∣ Aₜ`.
    EVIDENCE: `A 2 1 = 2` (`= 2·1`), `A 2 2 = 54 = 2·27`, `A 3 1 = 57 = 3·19`;
    all are `q·(unit mod q)`.  CONFIRMED → `A_qadic_valuation`.

H3 (Analyst). Consequence: `p = q` is *never* a divisor supplying `n = qᵗ·p`, so
    the conjecture's requirement `p ≠ q` is automatic from arithmetic, not an
    extra genericity assumption.  The residual factor `Aₜ / q` (`= 1, 27, 19, …`)
    is where all candidate primes live; its factorisations seed
    `FUTURE_DIRECTIONS.md`.

FAILURE ANALYSIS: trying to compute `v_q(Aₜ)` directly via Kummer on `Aₜ` failed
(`Aₜ` is not a binomial coefficient).  The working route is the *difference*
argument: bound the two summands' valuations separately, which needs only
`t ≥ 1` to guarantee `qᵗ ≥ 2`.
-/

namespace CentralBinomialValuation

open Nat

/-- `Aₜ = C(q^{t+1}, qᵗ) − q^{qᵗ}`, as an integer (the subtraction may otherwise
truncate in `ℕ`). -/
def A (q t : ℕ) : ℤ := (Nat.choose (q ^ (t + 1)) (q ^ t) : ℤ) - (q : ℤ) ^ (q ^ t)

/-
**Central prime-power binomial valuation.** For every prime `q` and `t`,
the base `q` divides `C(q^{t+1}, qᵗ)` exactly once.
-/

/-
**`q`-adic valuation of `Aₜ`.** For a prime base `q` and `t ≥ 1`, the base `q`
divides `Aₜ` exactly once: `q ∣ Aₜ` but `q² ∤ Aₜ`.
-/

end CentralBinomialValuation


