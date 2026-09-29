-- Prove2me | solution 1 for ScaleSmoothness.prod_one_add_le_inv
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:13:29.028694+00:00
-- url     : https://prove2.me/submissions/7b76524a-4508-4165-913f-34086d0b7f6d

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
omit [Fintype ι] in
theorem solution(s : Finset ι) (x : ι → ℚ) (hx : ∀ i, 0 ≤ x i)
    (h : ∑ i ∈ s, x i < 1) : ∏ i ∈ s, (1 + x i) ≤ 1 / (1 - ∑ i ∈ s, x i) := by
  induction s using Finset.induction with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj] at h ⊢
    rw [Finset.prod_insert hj]
    have hsnn : 0 ≤ ∑ i ∈ s, x i := Finset.sum_nonneg fun i _ => hx i
    have hs1 : ∑ i ∈ s, x i < 1 := by have := hx j; linarith
    have hIH := ih hs1
    have hpos : (0 : ℚ) < 1 - ∑ i ∈ s, x i := by linarith
    have hpos2 : (0 : ℚ) < 1 - (x j + ∑ i ∈ s, x i) := by linarith
    have hstep : (1 + x j) * (1 / (1 - ∑ i ∈ s, x i)) ≤ 1 / (1 - (x j + ∑ i ∈ s, x i)) := by
      rw [mul_one_div, div_le_div_iff₀ hpos hpos2]
      nlinarith [hx j, hsnn]
    calc (1 + x j) * ∏ i ∈ s, (1 + x i)
        ≤ (1 + x j) * (1 / (1 - ∑ i ∈ s, x i)) := by
          have : (0 : ℚ) ≤ 1 + x j := by have := hx j; linarith
          exact mul_le_mul_of_nonneg_left hIH this
      _ ≤ 1 / (1 - (x j + ∑ i ∈ s, x i)) := hstep
