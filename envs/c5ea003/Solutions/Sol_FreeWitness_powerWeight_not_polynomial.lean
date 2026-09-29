-- Prove2me | solution 1 for FreeWitness.powerWeight_not_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T15:29:58.984605+00:00
-- url     : https://prove2.me/submissions/5d9e3b89-2eb7-4431-8555-89c1ee17f3e1

-- Sol generated from MachineLearning/FreeWitnessClassification.lean
import Mathlib
import Definitions.Def_MachineLearning_FreeWitnessTraceLemma
import Definitions.Def_MachineLearning_HalfPlaneCRTSeparable
import Theorems.Thm_FreeWitness_comp_eq_of_witness_poly
import Theorems.Thm_FreeWitness_two_mul_six_pow_le

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


/-- The arithmetic separation at the heart of the rigidity argument:
`6^k + 5^k < 10^k + 3^k` for every `k ≥ 1`. -/
lemma six_pow_add_five_pow_lt (k : ℕ) (hk : 1 ≤ k) : 6 ^ k + 5 ^ k < 10 ^ k + 3 ^ k := by
  rcases Nat.lt_or_ge k 2 with hk1 | hk2
  · interval_cases k
    · norm_num
  · have h5 : (5 : ℕ) ^ k ≤ 6 ^ k := Nat.pow_le_pow_left (by omega) k
    have h := two_mul_six_pow_le k hk2
    have h3 : 0 < (3 : ℕ) ^ k := Nat.pow_pos (by omega)
    omega




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
theorem solution(F : SemiprimeWitness) {k : ℕ} {c : ℤ}
    (hk : 1 ≤ k) (hc : c ≠ 0)
    (hw : ∀ s : ℕ, s.Prime → s ≠ 2 → F.w s = (s : ℤ) ^ k + c) :
    ∀ P : Polynomial ℤ, ¬ (∀ p q : ℕ, p.Prime → q.Prime → p ≠ 2 → q ≠ 2 → p ≠ q →
      F.W (p * q) = P.eval ((p : ℤ) * q)) := by
  intro P hP
  have h3 := comp_eq_of_witness_poly F hw hP (r := 3) (by norm_num) (by norm_num)
  have h5 := comp_eq_of_witness_poly F hw hP (r := 5) (by norm_num) (by norm_num)
  have e3 : P.eval 30 = ((3 : ℤ) ^ k + c) * (10 ^ k + c) := by
    have := congrArg (fun R => Polynomial.eval (10 : ℤ) R) h3
    simpa using this
  have e5 : P.eval 30 = ((5 : ℤ) ^ k + c) * (6 ^ k + c) := by
    have := congrArg (fun R => Polynomial.eval (6 : ℤ) R) h5
    simpa using this
  have h30 : ((3 : ℤ) ^ k + c) * (10 ^ k + c) = ((5 : ℤ) ^ k + c) * (6 ^ k + c) := by
    rw [← e3, ← e5]
  have hmul1 : (3 : ℤ) ^ k * 10 ^ k = 30 ^ k := by rw [← mul_pow]; norm_num
  have hmul2 : (5 : ℤ) ^ k * 6 ^ k = 30 ^ k := by rw [← mul_pow]; norm_num
  have hkey : c * ((10 : ℤ) ^ k + 3 ^ k) = c * (6 ^ k + 5 ^ k) := by nlinarith [h30, hmul1, hmul2]
  have key : (10 : ℤ) ^ k + 3 ^ k = 6 ^ k + 5 ^ k := mul_left_cancel₀ hc hkey
  have hnat : (6 : ℕ) ^ k + 5 ^ k < 10 ^ k + 3 ^ k := six_pow_add_five_pow_lt k hk
  have hZ : (6 : ℤ) ^ k + 5 ^ k < 10 ^ k + 3 ^ k := by exact_mod_cast hnat
  linarith [key, hZ]
