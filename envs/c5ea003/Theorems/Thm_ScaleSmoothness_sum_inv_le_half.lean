-- Prove2me | Theorems.Thm_ScaleSmoothness_sum_inv_le_half
-- name    : ScaleSmoothness.sum_inv_le_half
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T22:51:47.302195+00:00
-- url     : https://prove2.me/theorems/f79a3a1c-23e1-410c-a4a5-f072a0804961
-- title:
--   For any finite set of naturals `≥ 3`, `∑ 1/(n(n−1)) ≤ 1/2`.
-- statement:
--   For any finite set of naturals `≥ 3`, `∑ 1/(n(n−1)) ≤ 1/2`.
--
--   ```lean
--   theorem ScaleSmoothness.sum_inv_le_half(S : Finset ℕ) (hS : ∀ n ∈ S, 3 ≤ n) :
--       ∑ n ∈ S, (1 : ℚ) / ((n : ℚ) * ((n : ℚ) - 1)) ≤ 1 / 2 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `NumberTheory/ScaleSmoothnessDispersion.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/NumberTheory/ScaleSmoothnessDispersion.lean#L173

-- Thm stub generated from NumberTheory/ScaleSmoothnessDispersion.lean
import Mathlib
import Definitions.Def_NumberTheory_QRDialLocalStatistics
import Definitions.Def_NumberTheory_ScaleSmoothnessDispersion

/-!
# Global structure correction for `x² − N`: mean one, and uniformly bounded dispersion

This is the global half of the round-73 #4 (exp 562) **RANDOM-AT-SCALE** finding.
`Catalog.NumberTheory.QRDialLocalStatistics` computed, prime by prime, the exact
distribution of the local correction

  `localFactor p N = (p − dial p N)/(p − 1)`

by which the `p`-part of the smoothness density of `x² − N` differs from that of
a random integer.  Multiplying over the primes `p ≤ B` gives the *structure
correction*

  `structureCorrection a N = ∏_{i} localFactor (a i) (N i)`,

the full multiplicative factor relating the (Dickman-type) heuristic smoothness
probability of `x² − N` to that of a size-matched random integer.

## Main results

* `sum_structureCorrection` — **mean exactly one**.  Averaged over the residue
  data `N`, the structure correction is exactly `1`, for *every* finite family
  of odd primes.  Formalises the experimental null `r(u) = 1`: quadratic-sieve
  polynomials carry no ensemble-level smoothness edge, at any `u`.
* `sum_structureCorrection_crt` — the same statement genuinely averaged over
  `N mod ∏ p` via the Chinese remainder theorem.
* `sum_structureCorrection_sq`, `sum_structureCorrection_centred_sq` — the
  variance is exactly `dispersionBound a − 1` with
  `dispersionBound a = ∏_p (1 + 1/(p(p−1)))`.
* `dispersionBound_le_two` — **uniform dispersion bound**: for any finite set of
  distinct odd primes, `dispersionBound a ≤ 2`, however large the smoothness
  bound `B`.  The measured per-`N` overdispersion `D = 1.61 [1.50,1.73]` sits
  inside this a-priori ceiling; the numerical value of the infinite product over
  all odd primes is ≈ `1.30`.
* `chebyshev_structureCorrection` — a finite Chebyshev inequality: the fraction
  of `N` whose structure correction deviates from `1` by at least `t` is at most
  `(dispersionBound a − 1)/t² ≤ 1/t²`.
* `no_first_order_smoothness_edge` — the packaged null statement: mean exactly
  one *and* deviation mass controlled uniformly in the prime family.

Everything is exact and rational; no analytic estimate is used anywhere.
-/

open ScaleSmoothness

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]




variable (a : ι → ℕ) [∀ i, Fact (a i).Prime] (hodd : ∀ i, a i ≠ 2)

include hodd








/-! ### The Chinese-remainder form: averaging over `N mod ∏ p` -/



/-! ### A uniform ceiling on the dispersion -/

theorem ScaleSmoothness.sum_inv_le_half(S : Finset ℕ) (hS : ∀ n ∈ S, 3 ≤ n) :
    ∑ n ∈ S, (1 : ℚ) / ((n : ℚ) * ((n : ℚ) - 1)) ≤ 1 / 2 := by sorry
