-- Prove2me | solution 1 for FreeWitness.two_mul_six_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T15:27:48.665215+00:00
-- url     : https://prove2.me/submissions/cebb709b-6f2c-4ce5-ab52-79953f66a450

-- Sol generated from MachineLearning/FreeWitnessClassification.lean
import Mathlib
import Definitions.Def_MachineLearning_FreeWitnessTraceLemma

/-!
# The classification theorem for power-shaped free witnesses

Cycle 2.  `FreeWitnessTraceLemma.lean` isolated the abstract mechanism; this file proves
the two halves of the classification *simultaneously and in general*, for every witness
whose local weight has the affine-power shape `w x = a x^k + c`:

* **Factoring-completeness** (`SemiprimeWitness.affinePower_recovery`): the aggregate
  determines the power sum `p^k + q^k`, hence — through the three recovery channels
  below — the factorisation.

* **Non-polynomiality** (`powerWeight_not_polynomial`): for `k ≥ 1` and `c ≠ 0` no
  integer polynomial in `N` agrees with the aggregate on all odd semiprimes.  This is a
  rigidity theorem, proved from the infinitude of primes: fixing one prime `r` forces
  `P(r X) = (r^k + c)(X^k + c)` as an identity of polynomials, and the two evaluations
  `P(3 · 10) = P(5 · 6)` then collide, because `10^k + 3^k ≠ 6^k + 5^k` for `k ≥ 1`.
  So a *non-polynomial local weight forces a non-polynomial aggregate* — the exact
  implication asserted, but not proved, in the source paper.

* **The three recovery channels of the trace lemma** (§2 of the paper) are all shown to
  be complete: `two_mul_max_eq` (trace ⇒ `max(p,q)`), `factor_of_max` (`max` ⇒ the other
  factor), `residue_channel` (a residue vector modulo a large enough modulus ⇒ the
  factor).  Together with `pair_determined_of_sum_prod` this is the statement that the
  information content of a recoverable witness is exactly one factor-secret coordinate.

* `classification_of_powerWeight` packages both halves into a single statement.
-/

open FreeWitness

open Polynomial

/-! ## Affine-power local weights: recovery -/

open SemiprimeWitness

variable (F : SemiprimeWitness)



/-! ## The three recovery channels -/




/-! ## Non-polynomiality of every power-shaped witness -/






/-! ### Lab notes (cycle 2)

Rigidity evaluation table (the two candidate values of `P(30)`), for the local weight
`x^k + c`:

```
k :  1        2         3           c-coefficient identity forced
     (3+c)(10+c) = (5+c)(6+c)   →  13c = 11c   → c = 0
     (9+c)(100+c) = (25+c)(36+c) → 109c = 61c  → c = 0
     (27+c)(1000+c) = (125+c)(216+c) → 1027c = 341c → c = 0
```
In every case `10^k + 3^k > 6^k + 5^k`, so `c = 0`: a non-trivial constant term in the
local weight is incompatible with a polynomial closed form in `N`.
-/

example : (10 : ℕ) ^ 1 + 3 ^ 1 ≠ 6 ^ 1 + 5 ^ 1 := by norm_num

example : (10 : ℕ) ^ 3 + 3 ^ 3 ≠ 6 ^ 3 + 5 ^ 3 := by norm_num


open FreeWitness in
theorem solution(k : ℕ) (hk : 2 ≤ k) : 2 * 6 ^ k ≤ 10 ^ k := by
  induction k with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge n 2 with hn | hn
    · interval_cases n
      · omega
      · norm_num
    · have h := ih (by omega)
      calc 2 * 6 ^ (n + 1) = 6 * (2 * 6 ^ n) := by ring
        _ ≤ 6 * 10 ^ n := Nat.mul_le_mul_left 6 h
        _ ≤ 10 * 10 ^ n := Nat.mul_le_mul_right _ (by omega)
        _ = 10 ^ (n + 1) := by ring
