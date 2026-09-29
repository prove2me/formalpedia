-- Prove2me | Definitions.Def_NumberTheory_ScaleSmoothnessDispersion
-- name    : NumberTheory_ScaleSmoothnessDispersion
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:17:36.733436+00:00
-- url     : https://prove2.me/theorems/f1117412-e6ac-4ca8-97c0-867faed01f49
-- title:
--   Aether Catalog definitions — NumberTheory_ScaleSmoothnessDispersion
-- statement:
--   Definition bundle for the Aether Catalog module `NumberTheory.ScaleSmoothnessDispersion`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from NumberTheory/ScaleSmoothnessDispersion.lean by skeleton subtraction
import Mathlib
import Definitions.Def_NumberTheory_QRDialLocalStatistics

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

namespace ScaleSmoothness

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The **structure correction**: the product over the primes of the family of the
local corrections.  A random integer has `structureCorrection = 1` identically. -/
def structureCorrection (a : ι → ℕ) [∀ i, NeZero (a i)] (N : ∀ i, ZMod (a i)) : ℚ :=
  ∏ i, localFactor (a i) (N i)

/-- The **dispersion ceiling** `∏_p (1 + 1/(p(p−1)))`: the exact second moment of the
structure correction. -/
def dispersionBound (a : ι → ℕ) : ℚ :=
  ∏ i, (1 + 1 / ((a i : ℚ) * ((a i : ℚ) - 1)))

section Family

variable (a : ι → ℕ) [∀ i, Fact (a i).Prime] (hodd : ∀ i, a i ≠ 2)

include hodd







end Family

/-! ### The Chinese-remainder form: averaging over `N mod ∏ p` -/

instance neZero_prod_primes (a : ι → ℕ) [∀ i, Fact (a i).Prime] : NeZero (∏ i, a i) :=
  ⟨Finset.prod_ne_zero_iff.2 fun i _ => (Fact.out : (a i).Prime).ne_zero⟩


/-! ### A uniform ceiling on the dispersion -/








/-! ### The QR dial at the global level, and strict (but bounded) clustering -/



/-! ### Non-vacuity: the family `{3, 5, 7}` -/

namespace Example357

/-- The family of the three smallest odd primes. -/
def a : Fin 3 → ℕ := ![3, 5, 7]

instance factPrime : ∀ i, Fact (Nat.Prime (a i)) := by
  intro i
  fin_cases i <;> exact ⟨by norm_num [a]⟩






end Example357

end ScaleSmoothness


