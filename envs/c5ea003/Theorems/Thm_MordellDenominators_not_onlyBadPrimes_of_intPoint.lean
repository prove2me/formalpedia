-- Prove2me | Theorems.Thm_MordellDenominators_not_onlyBadPrimes_of_intPoint
-- name    : MordellDenominators.not_onlyBadPrimes_of_intPoint
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:56:38.550073+00:00
-- url     : https://prove2.me/theorems/63f33adf-7574-4799-9337-7c6b4b1c4643
-- title:
--   **Every integral point with a good prime in its `y`-coordinate refutes the
-- statement:
--   **Every integral point with a good prime in its `y`-coordinate refutes the
--   conjecture.**
--
--   ```lean
--   theorem MordellDenominators.not_onlyBadPrimes_of_intPoint{N x y : ℤ} (h : y ^ 2 = x ^ 3 + N)
--       (hy : y ≠ 0) {l : ℕ} (hl : l.Prime) (hly : (l : ℤ) ∣ y)
--       (hlN : ¬ ((l : ℤ) ∣ 6 * N)) :
--       ¬ OnlyBadPrimes N ((x : ℚ), (y : ℚ)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/MordellDenominators/Criterion.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/MordellDenominators/Criterion.lean#L77

-- Thm stub generated from Cryptography/MordellDenominators/Criterion.lean
import Mathlib
import Definitions.Def_Cryptography_MordellDenominators_Basic

/-!
# A counterexample machine

Both the numerical counterexample (`Counterexample.lean`) and the infinite
family (`Family.lean`) are instances of one criterion, proved here.

**Criterion.**  Let `P = (x, y)` be an *integral* point of `E_N : y² = x³ + N`
with `y ≠ 0`, and let `ℓ` be a prime with `ℓ ∣ y` and `ℓ ∤ 6N`.  Then `ℓ`
divides the denominator of `x(2P)`, so the "only bad primes" conjecture fails
for `(N, P)`.

The proof is a two-line valuation computation once the duplication formula is
written over `ℤ`: the denominator of `x(2P)` is (a divisor of) `4y²`, which `ℓ`
divides, while the numerator `x⁴ - 8Nx = x(y² - 9N)` is prime to `ℓ` precisely
because `ℓ ∤ 6N`.  Thus **every** integral point whose `y`-coordinate has a
prime factor of good reduction refutes the conjecture — such points are
ubiquitous, which is why the conjecture fails 100% of the time in experiments.
-/

open MordellDenominators

theorem MordellDenominators.not_onlyBadPrimes_of_intPoint{N x y : ℤ} (h : y ^ 2 = x ^ 3 + N)
    (hy : y ≠ 0) {l : ℕ} (hl : l.Prime) (hly : (l : ℤ) ∣ y)
    (hlN : ¬ ((l : ℤ) ∣ 6 * N)) :
    ¬ OnlyBadPrimes N ((x : ℚ), (y : ℚ)) := by sorry
