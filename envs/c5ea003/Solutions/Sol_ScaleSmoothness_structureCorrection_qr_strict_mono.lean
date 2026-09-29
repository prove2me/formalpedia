-- Prove2me | solution 1 for ScaleSmoothness.structureCorrection_qr_strict_mono
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:28:47.391293+00:00
-- url     : https://prove2.me/submissions/7ad9dbf0-580a-4091-b263-48fb356df9bc

-- Sol generated from NumberTheory/ScaleSmoothnessDispersion.lean
import Mathlib
import Definitions.Def_NumberTheory_QRDialLocalStatistics
import Definitions.Def_NumberTheory_ScaleSmoothnessDispersion
import Theorems.Thm_ScaleSmoothness_localFactor_lt_of_qr
import Theorems.Thm_ScaleSmoothness_localFactor_pos

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
theorem solution(a : ι → ℕ) [∀ i, Fact (a i).Prime]
    (hodd : ∀ i, a i ≠ 2) {N N' : ∀ i, ZMod (a i)} {j : ι}
    (hagree : ∀ i, i ≠ j → N i = N' i)
    (hQ : dial (a j) (N j) = 2) (hNQ : dial (a j) (N' j) = 0) :
    structureCorrection a N < structureCorrection a N' := by
  have hrest : ∏ i ∈ univ.erase j, localFactor (a i) (N i)
      = ∏ i ∈ univ.erase j, localFactor (a i) (N' i) :=
    Finset.prod_congr rfl fun i hi => by
      rw [hagree i (Finset.mem_erase.1 hi).1]
  have hpos : (0 : ℚ) < ∏ i ∈ univ.erase j, localFactor (a i) (N i) :=
    Finset.prod_pos fun i _ => localFactor_pos (a i) (hodd i) _
  have hj : localFactor (a j) (N j) < localFactor (a j) (N' j) :=
    localFactor_lt_of_qr (a j) (hodd j) hQ hNQ
  have hsplitN : structureCorrection a N
      = localFactor (a j) (N j) * ∏ i ∈ univ.erase j, localFactor (a i) (N i) :=
    (Finset.mul_prod_erase (univ : Finset ι) (fun i => localFactor (a i) (N i))
      (mem_univ j)).symm
  have hsplitN' : structureCorrection a N'
      = localFactor (a j) (N' j) * ∏ i ∈ univ.erase j, localFactor (a i) (N' i) :=
    (Finset.mul_prod_erase (univ : Finset ι) (fun i => localFactor (a i) (N' i))
      (mem_univ j)).symm
  rw [hsplitN, hsplitN', ← hrest]
  exact mul_lt_mul_of_pos_right hj hpos
