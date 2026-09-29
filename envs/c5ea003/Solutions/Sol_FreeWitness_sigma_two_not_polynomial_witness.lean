-- Prove2me | solution 1 for FreeWitness.sigma_two_not_polynomial_witness
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T15:31:55.666208+00:00
-- url     : https://prove2.me/submissions/63b0a1f2-403c-4585-840e-7327941df49a

-- Sol generated from MachineLearning/FreeWitnessSigmaK.lean
import Mathlib
import Definitions.Def_MachineLearning_FreeWitnessSigmaK
import Theorems.Thm_FreeWitness_not_polynomial_of_not_dvd

/-!
# SIGK: the predicted free witness `σ_k`, and the polynomial barrier for it

The classification of `16_FreeWitness_Classification.md` makes a falsifiable prediction:
*any* non-polynomial CRT-multiplicative local weight yields a free witness, and the
divisor power sum `σ_k(N) = ∑_{d ∣ N} d^k`, whose local weight is `1 + p^k`, should be
one.  This file proves the prediction, in the strong form that the paper only reports as
"verified computationally":

* `sigma_prime`, `sigma_semiprime` — the local weight and the CRT factorisation
  `σ_k(pq) = (1 + p^k)(1 + q^k)` for distinct primes.

* `sigmaWitness` — `σ_k` as a `FreeWitness.SemiprimeWitness` with power-shaped local
  weight `x ^ k + 1`, so the abstract trace lemma of `FreeWitnessTraceLemma.lean`
  applies verbatim.

* `sigma_power_sum`, `sigma_one_trace`, `sigma_two_trace_sq`, `sigma_two_trace_nat` —
  the recovery formulas: `p^k + q^k = σ_k(N) - N^k - 1`; for `k = 1` the trace itself,
  for `k = 2` the identity `(p+q)^2 + 1 + N^2 = σ_2(N) + 2N` and the explicit square
  root `p + q = √(σ_2(N) + 2N - 1 - N²)`.

* `sigma_two_recovers_factors` — the full factorisation is determined: any positive pair
  with the same product and the same witness-derived trace *is* `{p, q}`.

* `sigma_not_polynomial` — **the hard half.**  For every `k ≥ 1` there is *no* integer
  polynomial `P` with `σ_k(pq) = P(pq)` for all pairs of distinct primes.  This is the
  instance `c = 1` of the general rigidity theorem
  `FreeWitness.powerWeight_not_polynomial` of `FreeWitnessClassification.lean`: fixing
  one prime `r` and letting the other run over the infinitely many primes forces the
  polynomial identity `P(r X) = (1 + r^k)(1 + X^k)`; the `r = 3` identity at `10` and the
  `r = 5` identity at `6` give two values for `P(30)` whose equality would force
  `10^k + 3^k = 6^k + 5^k`, which fails for every `k ≥ 1`.

* `sigma_two_not_polynomial_witness` — the same conclusion by the cheap congruence
  route of `FreeWitness.not_polynomial_of_not_dvd`: `33 - 15 = 18` does not divide
  `σ_2(33) - σ_2(15) = 960`.

Together with `FreeWitnessTraceLemma.lean` this makes the two structural claims of the
classification precise for the SIGK family: the witness is *factoring-complete*
(it hands over the trace) and *non-polynomial* in the modulus.
-/

open FreeWitness

open ArithmeticFunction Polynomial

/-! ## The local weight and the CRT factorisation -/






/-! ## Recovery: the trace lemma for `σ_k` -/







/-! ## The polynomial barrier for `σ_k` -/



/-! ### Lab notes (cycle 2: SIGK)

```
N = p·q   σ₂(N)   (1+p²)(1+q²)   p²+q² = σ₂-1-N²   trace √(σ₂+2N-1-N²)
15 = 3·5    260   10·26 = 260          34                8 = 3+5
21 = 3·7    500   10·50 = 500          58               10 = 3+7
33 = 3·11  1220   10·122 = 1220       130               14 = 3+11
35 = 5·7   1300   26·50 = 1300          74              12 = 5+7
77 = 7·11  6100   50·122 = 6100        170              18 = 7+11
```
Difference test for the polynomial barrier: `33 - 15 = 18`, `σ₂(33) - σ₂(15) = 960`,
and `18 ∤ 960`.  The rigidity proof upgrades this from one pair to all `k ≥ 1`.
-/

example : sigma 2 15 = 260 := by decide
example : sigma 2 21 = 500 := by decide
example : sigma 1 33 = 48 := by decide


open FreeWitness in
theorem solution:
    ∀ P : Polynomial ℤ, ¬ (∀ n ∈ ({15, 33} : Set ℕ),
      ((sigma 2 n : ℕ) : ℤ) = P.eval (n : ℤ)) := by
  have h33 : sigma 2 33 = 1220 := by
    have : (33 : ℕ) = 3 * 11 := by norm_num
    rw [this, sigma_semiprime (by norm_num) (by norm_num) (by norm_num)]
    norm_num
  have h15 : sigma 2 15 = 260 := by
    have : (15 : ℕ) = 3 * 5 := by norm_num
    rw [this, sigma_semiprime (by norm_num) (by norm_num) (by norm_num)]
    norm_num
  refine not_polynomial_of_not_dvd (W := fun n => ((sigma 2 n : ℕ) : ℤ))
    (S := ({15, 33} : Set ℕ)) (N₁ := 33) (N₂ := 15) (by simp) (by simp) ?_
  simp only [h33, h15]
  norm_num
