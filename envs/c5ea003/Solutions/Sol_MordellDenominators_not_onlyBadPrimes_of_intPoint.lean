-- Prove2me | solution 1 for MordellDenominators.not_onlyBadPrimes_of_intPoint
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T06:29:05.68452+00:00
-- url     : https://prove2.me/submissions/5255462b-d7c1-4477-9499-9b29e7925d77

-- Sol generated from Cryptography/MordellDenominators/Criterion.lean
import Mathlib
import Definitions.Def_Cryptography_MordellDenominators_Basic
import Theorems.Thm_MordellDenominators_dblIter_one_fst
import Theorems.Thm_MordellDenominators_good_prime_dvd_den_dblX

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






open MordellDenominators in
theorem solution{N x y : ℤ} (h : y ^ 2 = x ^ 3 + N)
    (hy : y ≠ 0) {l : ℕ} (hl : l.Prime) (hly : (l : ℤ) ∣ y)
    (hlN : ¬ ((l : ℤ) ∣ 6 * N)) :
    ¬ OnlyBadPrimes N ((x : ℚ), (y : ℚ)) := by
  intro hcon
  refine hlN (hcon 1 l hl ?_)
  rw [dblIter_one_fst]
  exact good_prime_dvd_den_dblX h hy hl hly hlN
