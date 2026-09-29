-- Prove2me | Theorems.Thm_fib_primitive_divisor_prime
-- name    : fib_primitive_divisor_prime
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:54:26.241737+00:00
-- url     : https://prove2.me/theorems/e1cecdf5-155a-4795-9cd7-4aeb626eca11
-- title:
--   Carmichael's theorem, prime case.
-- statement:
--   **Carmichael's theorem, prime case.**  For prime `n â¥ 13`, `F(n)` has a
--   primitive prime divisor.
--
--   ```lean
--   theorem fib_primitive_divisor_prime(n : ℕ) (hn : 13 ≤ n) (hnp : Nat.Prime n) :
--       ∃ p, Nat.Prime p ∧ p ∣ Nat.fib n ∧
--         ∀ k, 0 < k → k < n → ¬(p ∣ Nat.fib k) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/CarmichaelHelper.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/CarmichaelHelper.lean#L33

-- Thm stub generated from Shared/CarmichaelHelper.lean
import Mathlib

/-! # Carmichael's theorem: the prime case

We prove that for a **prime** `n ≥ 13`, the Fibonacci number `F(n)` has a
*primitive* prime divisor: a prime `p` dividing `F(n)` but dividing no earlier
`F(k)` with `0 < k < n`.

The prime case is elementary.  Because `n` is prime, the only proper positive
divisor of `n` is `1`.  If a prime `p` divides both `F(n)` and `F(k)` for some
`0 < k < n`, then (using the strong divisibility property
`Nat.fib_gcd`) `p` divides `F(gcd n k)`.  But `gcd n k` divides the prime `n`
and is `< n`, so it equals `1`, forcing `p ∣ F(1) = 1`, a contradiction.  Since
`F(n) > 1` it has a prime divisor, and every such divisor is primitive.

This is the "prime half" that complements the computational/structural composite
case in `Shared.CarmichaelProof`.

-- !-- Lab Notes -- !--
* **Hypothesis (Hypothesizer).**  For prime `n`, *every* prime divisor of `F(n)`
  should already be primitive, since there are no nontrivial proper divisors of
  `n` to host an earlier occurrence.
* **Experiment (Experimenter).**  Formalized the `gcd`-collapse argument through
  `Nat.fib_gcd` and `Nat.Coprime`.  The single delicate point is `F(n) > 1`,
  handled by `Nat.fib` monotonicity from `n ≥ 13 ≥ 3`.
* **Analysis (Analyst).**  "True and clean": the primitivity is automatic; the
  only existence input is a prime factor of `F(n)`, from `Nat.exists_prime_and_dvd`.
* **Critique (Critic).**  Corner case `k = n` is excluded by `k < n`; `k = 0` is
  excluded by `0 < k`.  No hidden use of the composite machinery.
* **Synthesis (PI).**  Prime `n` is the base of Carmichael's theorem; the
  composite case reduces to controlling shared factors across proper divisors.
-/

theorem fib_primitive_divisor_prime(n : ℕ) (hn : 13 ≤ n) (hnp : Nat.Prime n) :
    ∃ p, Nat.Prime p ∧ p ∣ Nat.fib n ∧
      ∀ k, 0 < k → k < n → ¬(p ∣ Nat.fib k) := by sorry
