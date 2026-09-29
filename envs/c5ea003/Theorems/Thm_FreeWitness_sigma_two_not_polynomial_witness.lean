-- Prove2me | Theorems.Thm_FreeWitness_sigma_two_not_polynomial_witness
-- name    : FreeWitness.sigma_two_not_polynomial_witness
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T15:23:11.313539+00:00
-- url     : https://prove2.me/theorems/e712c19d-c39c-4029-a6e3-35039ac0800b
-- title:
--   The same conclusion for `k = 2` by the cheap congruence route: `33 - 15 = 18` does
-- statement:
--   The same conclusion for `k = 2` by the cheap congruence route: `33 - 15 = 18` does
--   not divide `σ_2(33) - σ_2(15) = 1220 - 260 = 960`.  (A single pair of moduli suffices,
--   which is exactly the "mod `2^k` separation" strategy of §5 of the paper.)
--
--   ```lean
--   theorem FreeWitness.sigma_two_not_polynomial_witness:
--       ∀ P : Polynomial ℤ, ¬ (∀ n ∈ ({15, 33} : Set ℕ),
--         ((sigma 2 n : ℕ) : ℤ) = P.eval (n : ℤ)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/FreeWitnessSigmaK.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/FreeWitnessSigmaK.lean#L148

-- Thm stub generated from MachineLearning/FreeWitnessSigmaK.lean
import Mathlib
import Definitions.Def_MachineLearning_FreeWitnessSigmaK

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

theorem FreeWitness.sigma_two_not_polynomial_witness:
    ∀ P : Polynomial ℤ, ¬ (∀ n ∈ ({15, 33} : Set ℕ),
      ((sigma 2 n : ℕ) : ℤ) = P.eval (n : ℤ)) := by sorry
