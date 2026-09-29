-- Prove2me | solution 1 for ScaleSmoothness.sum_inv_consecutive
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:13:29.583986+00:00
-- url     : https://prove2.me/submissions/2acb9dde-f420-4a06-a0be-558df0ce4e41

-- Sol generated from NumberTheory/ScaleSmoothnessDispersion.lean
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



/-! ### Non-vacuity: the family `{3, 5, 7}` -/

open Example357










open ScaleSmoothness in
theorem solution(M : ℕ) (hM : 3 ≤ M) :
    ∑ n ∈ Finset.Icc 3 M, (1 : ℚ) / ((n : ℚ) * ((n : ℚ) - 1)) = 1 / 2 - 1 / (M : ℚ) := by
  induction M with
  | zero => omega
  | succ m ih =>
    rcases Nat.lt_or_ge m 3 with hm | hm
    · interval_cases m
      · omega
      · omega
      · norm_num
    · rw [Finset.sum_Icc_succ_top (by omega), ih (by omega)]
      have hm0 : (3 : ℚ) ≤ (m : ℚ) := by exact_mod_cast hm
      have h1 : (m : ℚ) ≠ 0 := by linarith
      have h2 : ((m : ℚ) + 1) ≠ 0 := by linarith
      push_cast
      rw [show ((m : ℚ) + 1 - 1) = (m : ℚ) by ring]
      field_simp
      ring
