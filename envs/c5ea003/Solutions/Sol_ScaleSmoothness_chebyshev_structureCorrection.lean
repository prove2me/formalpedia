-- Prove2me | solution 1 for ScaleSmoothness.chebyshev_structureCorrection
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:13:28.52914+00:00
-- url     : https://prove2.me/submissions/69597f23-7917-4bff-b1e3-169f62cd2a57

-- Sol generated from NumberTheory/ScaleSmoothnessDispersion.lean
import Mathlib
import Definitions.Def_NumberTheory_QRDialLocalStatistics
import Definitions.Def_NumberTheory_ScaleSmoothnessDispersion
import Theorems.Thm_ScaleSmoothness_card_pi_zmod
import Theorems.Thm_ScaleSmoothness_prod_second_moment_eq
import Theorems.Thm_ScaleSmoothness_sum_structureCorrection
import Theorems.Thm_ScaleSmoothness_sum_structureCorrection_sq

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






/-- **Exact variance of the structure correction.**  The centred second moment is
`(number of residue data) × (dispersionBound a − 1)`; i.e. the variance of the
structure correction is exactly `∏_p (1 + 1/(p(p−1))) − 1`.  This is the exact
source of the per-`N` clustering measured as `D = 1.61`. -/
theorem sum_structureCorrection_centred_sq :
    ∑ N : (∀ i, ZMod (a i)), (structureCorrection a N - 1) ^ 2 =
      (∏ i, (a i : ℚ)) * (dispersionBound a - 1) := by
  have expand : ∀ N : (∀ i, ZMod (a i)), (structureCorrection a N - 1) ^ 2 =
      (structureCorrection a N) ^ 2 - 2 * structureCorrection a N + 1 := by
    intro N; ring
  simp only [expand]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    sum_structureCorrection a hodd, sum_structureCorrection_sq a hodd,
    prod_second_moment_eq a hodd, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [card_pi_zmod a]
  ring


/-! ### The Chinese-remainder form: averaging over `N mod ∏ p` -/



/-! ### A uniform ceiling on the dispersion -/








/-! ### The QR dial at the global level, and strict (but bounded) clustering -/



/-! ### Non-vacuity: the family `{3, 5, 7}` -/

open Example357










open ScaleSmoothness in
theorem solution(a : ι → ℕ) [∀ i, Fact (a i).Prime]
    (hodd : ∀ i, a i ≠ 2) {t : ℚ} (ht : 0 < t) :
    t ^ 2 * (#{N : (∀ i, ZMod (a i)) | t ≤ |structureCorrection a N - 1|} : ℚ) ≤
      (∏ i, (a i : ℚ)) * (dispersionBound a - 1) := by
  classical
  set S : Finset (∀ i, ZMod (a i)) := {N | t ≤ |structureCorrection a N - 1|} with hS
  have hmem : ∀ N ∈ S, t ^ 2 ≤ (structureCorrection a N - 1) ^ 2 := by
    intro N hN
    have h : t ≤ |structureCorrection a N - 1| := by
      simpa [hS] using hN
    have habs : |structureCorrection a N - 1| ^ 2 = (structureCorrection a N - 1) ^ 2 :=
      sq_abs _
    nlinarith [abs_nonneg (structureCorrection a N - 1)]
  have h1 : (#S : ℚ) * t ^ 2 ≤ ∑ N ∈ S, (structureCorrection a N - 1) ^ 2 := by
    calc (#S : ℚ) * t ^ 2 = ∑ _N ∈ S, t ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ N ∈ S, (structureCorrection a N - 1) ^ 2 :=
          Finset.sum_le_sum hmem
  have h2 : ∑ N ∈ S, (structureCorrection a N - 1) ^ 2 ≤
      ∑ N : (∀ i, ZMod (a i)), (structureCorrection a N - 1) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
      (fun N _ _ => sq_nonneg _)
  rw [sum_structureCorrection_centred_sq a hodd] at h2
  linarith [h1, h2]
