-- Prove2me | solution 1 for AsaiLargeSieve.largeSieve_of_periodic_gram_dvd
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T17:10:29.310646+00:00
-- url     : https://prove2.me/submissions/dbdd66d1-58ff-4a37-b7db-4911364c4e97

-- Sol generated from Novelty/AsaiMomentApplications.lean
import Mathlib
import Definitions.Def_Novelty_AsaiLargeSieve
import Definitions.Def_Novelty_AsaiLargeSieveGram
import Definitions.Def_Novelty_AsaiSecondMoment
import Theorems.Thm_AsaiLargeSieve_card_congruence_class_le_of_dvd
import Theorems.Thm_AsaiLargeSieve_largeSieve_of_schur
/-
# Periodic Gram matrices and large-value consequences of the Asai second moment

Two further layers on top of `Novelty.AsaiLargeSieve`, `Novelty.AsaiLargeSieveGram` and
`Novelty.AsaiSecondMoment`.

**1. The `k + N/q` shape of the large sieve constant.**  In the Asai/Petersson setting the
correlation sums `∑_f λ_f(m) conj(λ_f(n))` are (up to the Kloosterman term) supported on
`m ≡ n` modulo the level/conductor parameter, and the true large sieve constant is therefore
of the shape *diagonal times the number of congruent pairs*, i.e. `D·(1 + N/q)`, rather than
`D + eN`.  `AsaiLargeSieve.largeSieve_of_periodic_gram` proves exactly this, and it is where
the `N`-aspect of the paper's `(kD + N^{1+ε})`-type constant comes from.  The combinatorial
core is `AsaiLargeSieve.card_congruence_class_le`: a residue class modulo `q` meets `[0,N)` in
at most `N/q + 1` points.

**2. Large values of central `L`-values.**  A second moment bound immediately controls the
number of forms with a large central value (Chebyshev), giving the standard "almost all
`As(f) × φ` have small central value" consequence:
`#{f : |L f| ≥ T} ≤ (c₁+c₂) ν² J² B k / T²`.

Main results:

* `AsaiLargeSieve.card_congruence_class_le`
* `AsaiLargeSieve.largeSieve_of_periodic_gram`
* `AsaiLargeSieve.secondMoment_periodic` — the `D·(1+N/q)` second moment.
* `AsaiLargeSieve.card_large_values_le` — Chebyshev for the moment.
* `AsaiLargeSieve.card_large_central_values` — the large-value bound under the full
  hypothesis package of `AsaiSecondMoment.asai_second_moment_k_aspect`.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): the two error shapes appearing in large sieve inequalities,
`D + eN` (uniform error) and `D(1 + N/q)` (periodic support), are both instances of the Schur
row bound; and the second, not the first, is what governs the `N`-aspect of the Asai constant.

Experiment (Experimenter): both are now derived from `largeSieve_of_schur`.  The periodic
case needed the counting lemma, proved by the injection `n ↦ n / q` from a residue class in
`[0,N)` into `[0, N/q]`; the reconstruction `n = q(n/q) + n%q` makes the injectivity an `omega`
computation.  The Chebyshev step needs no positivity beyond `T > 0`.

Analysis (Analyst): the comparison of the two criteria is instructive.  For `q ≥ N` the
periodic bound gives `2D` while the uniform criterion gives `D + eN`; for `q` small the
periodic bound degrades linearly in `N/q`, matching the classical `N + q²`-type constants.
So the abstract framework reproduces both regimes, which is evidence that the Schur row bound
is the correct axiom to isolate from the Petersson formula.

Critique (Critic): the Chebyshev corollary is stated multiplicatively
(`card · T² ≤ bound`) rather than as `card ≤ bound / T²` to avoid any hidden division-by-zero
convention; with `T > 0` the two are equivalent, and the multiplicative form is also correct
when the bound is negative (in which case the hypothesis set is empty).
-/

open Finset Complex

open AsaiLargeSieve

variable {ι : Type*}

/-! ## The periodic criterion -/






/-! ## Large values -/




open AsaiLargeSieve in
theorem solution(S : Finset ι) (lam : ι → ℕ → ℂ) (N q : ℕ) (D : ℝ)
    (hdvd : q ∣ N) (hD : 0 ≤ D)
    (hoff : ∀ m ∈ Finset.range N, ∀ n ∈ Finset.range N, ¬ (m ≡ n [MOD q]) → gram S lam m n = 0)
    (hbnd : ∀ m ∈ Finset.range N, ∀ n ∈ Finset.range N, ‖gram S lam m n‖ ≤ D) :
    LargeSieve S lam N (D * ((N / q : ℕ) : ℝ)) := by
  classical
  refine largeSieve_of_schur S lam N _ ?_
  intro m hm
  have hsupp : ∑ n ∈ Finset.range N, ‖gram S lam m n‖
      = ∑ n ∈ (Finset.range N).filter (fun n => m ≡ n [MOD q]), ‖gram S lam m n‖ := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro n hn hnot
    have hnc : ¬ (m ≡ n [MOD q]) := fun hc => hnot (Finset.mem_filter.mpr ⟨hn, hc⟩)
    rw [hoff m hm n hn hnc, norm_zero]
  rw [hsupp]
  have hstep : ∑ n ∈ (Finset.range N).filter (fun n => m ≡ n [MOD q]), ‖gram S lam m n‖
      ≤ (((Finset.range N).filter (fun n => m ≡ n [MOD q])).card : ℝ) * D := by
    have hpt : ∀ n ∈ (Finset.range N).filter (fun n => m ≡ n [MOD q]),
        ‖gram S lam m n‖ ≤ D := fun n hn => hbnd m hm n (Finset.mem_filter.mp hn).1
    calc ∑ n ∈ (Finset.range N).filter (fun n => m ≡ n [MOD q]), ‖gram S lam m n‖
        ≤ ∑ _n ∈ (Finset.range N).filter (fun n => m ≡ n [MOD q]), D := Finset.sum_le_sum hpt
      _ = (((Finset.range N).filter (fun n => m ≡ n [MOD q])).card : ℝ) * D := by
          rw [Finset.sum_const, nsmul_eq_mul]
  refine hstep.trans ?_
  have hcast : (((Finset.range N).filter (fun n => m ≡ n [MOD q])).card : ℝ) ≤ ((N / q : ℕ) : ℝ) := by
    exact_mod_cast card_congruence_class_le_of_dvd hdvd m
  calc (((Finset.range N).filter (fun n => m ≡ n [MOD q])).card : ℝ) * D
      ≤ ((N / q : ℕ) : ℝ) * D := mul_le_mul_of_nonneg_right hcast hD
    _ = D * ((N / q : ℕ) : ℝ) := by ring
