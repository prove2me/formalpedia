-- Prove2me | Definitions.Def_MachineLearning_FreeWitnessSigmaK
-- name    : MachineLearning_FreeWitnessSigmaK
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T15:18:44.579324+00:00
-- url     : https://prove2.me/theorems/f6cfef37-587a-4455-aef5-abe53b1bd823
-- title:
--   Aether Catalog definitions — MachineLearning_FreeWitnessSigmaK
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.FreeWitnessSigmaK`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/FreeWitnessSigmaK.lean by skeleton subtraction
import Mathlib
import Definitions.Def_MachineLearning_FreeWitnessTraceLemma

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

namespace FreeWitness

open ArithmeticFunction Polynomial

/-! ## The local weight and the CRT factorisation -/

/-- The local weight of `σ_k` at a prime: `σ_k(p) = 1 + p ^ k`. -/
theorem sigma_prime {k p : ℕ} (hp : p.Prime) : (sigma k) p = 1 + p ^ k := by
  rw [sigma_apply, hp.divisors, Finset.sum_pair hp.one_lt.ne]
  simp

/-- **The SIGK prediction.**  For distinct primes, `σ_k(pq) = (1 + p^k)(1 + q^k)`:
the divisor power sum is CRT-multiplicative with non-polynomial local weight. -/
theorem sigma_semiprime {k p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    (sigma k) (p * q) = (1 + p ^ k) * (1 + q ^ k) := by
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  rw [isMultiplicative_sigma.map_mul_of_coprime hcop, sigma_prime hp, sigma_prime hq]

/-- `σ_k` as a CRT-multiplicative semiprime witness with power-shaped local weight. -/
def sigmaWitness (k : ℕ) : SemiprimeWitness where
  W N := ((sigma k N : ℕ) : ℤ)
  w x := (x : ℤ) ^ k + 1
  factorizes := by
    intro p q hp hq _ _ hpq
    rw [sigma_semiprime hp hq hpq]
    push_cast
    ring



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

end FreeWitness


