-- Prove2me | Theorems.Thm_ScaleSmoothness_one_lt_dispersionBound
-- name    : ScaleSmoothness.one_lt_dispersionBound
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T22:52:23.441693+00:00
-- url     : https://prove2.me/theorems/98ceb4a9-433b-47ae-b6ab-cf66439439c0
-- title:
--   Clustering is real.
-- statement:
--   **Clustering is real.**  For a nonempty family of odd primes the dispersion is
--   strictly larger than `1`: the structure correction is genuinely non-constant, so
--   the per-`N` smoothness rate is genuinely overdispersed relative to Poisson.
--   Together with `dispersionBound_le_two` this pins the phenomenon between `1` and
--   `2`.
--
--   ```lean
--   theorem ScaleSmoothness.one_lt_dispersionBound(a : ι → ℕ) [∀ i, Fact (a i).Prime] (hodd : ∀ i, a i ≠ 2)
--       (j : ι) : 1 < dispersionBound a := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `NumberTheory/ScaleSmoothnessDispersion.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/NumberTheory/ScaleSmoothnessDispersion.lean#L330

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








/-! ### The QR dial at the global level, and strict (but bounded) clustering -/

theorem ScaleSmoothness.one_lt_dispersionBound(a : ι → ℕ) [∀ i, Fact (a i).Prime] (hodd : ∀ i, a i ≠ 2)
    (j : ι) : 1 < dispersionBound a := by sorry
