-- Prove2me | Theorems.Thm_AsaiLargeSieve_largeSieve_of_periodic_gram_dvd
-- name    : AsaiLargeSieve.largeSieve_of_periodic_gram_dvd
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:00:53.522143+00:00
-- url     : https://prove2.me/theorems/dfd95a6a-17d1-4a75-8255-043e9820c332
-- title:
--   Sharpened periodic criterion when `q ∣ N`: the admissible constant is `D · (N/q)`,
-- statement:
--   **Sharpened periodic criterion** when `q ∣ N`: the admissible constant is `D · (N/q)`,
--   without the `+1` loss.  Numerically (see `ComputationalEvidence.md`) this is attained: for the
--   two-character system mod `2` with `N = 4` and `D = 2` the extremal ratio is exactly `4`.
--
--   ```lean
--   theorem AsaiLargeSieve.largeSieve_of_periodic_gram_dvd(S : Finset ι) (lam : ι → ℕ → ℂ) (N q : ℕ) (D : ℝ)
--       (hdvd : q ∣ N) (hD : 0 ≤ D)
--       (hoff : ∀ m ∈ Finset.range N, ∀ n ∈ Finset.range N, ¬ (m ≡ n [MOD q]) → gram S lam m n = 0)
--       (hbnd : ∀ m ∈ Finset.range N, ∀ n ∈ Finset.range N, ‖gram S lam m n‖ ≤ D) :
--       LargeSieve S lam N (D * ((N / q : ℕ) : ℝ)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/AsaiMomentApplications.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/AsaiMomentApplications.lean#L155

-- Thm stub generated from Novelty/AsaiMomentApplications.lean
import Mathlib
import Definitions.Def_Novelty_AsaiLargeSieve
import Definitions.Def_Novelty_AsaiLargeSieveGram
import Definitions.Def_Novelty_AsaiSecondMoment
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

theorem AsaiLargeSieve.largeSieve_of_periodic_gram_dvd(S : Finset ι) (lam : ι → ℕ → ℂ) (N q : ℕ) (D : ℝ)
    (hdvd : q ∣ N) (hD : 0 ≤ D)
    (hoff : ∀ m ∈ Finset.range N, ∀ n ∈ Finset.range N, ¬ (m ≡ n [MOD q]) → gram S lam m n = 0)
    (hbnd : ∀ m ∈ Finset.range N, ∀ n ∈ Finset.range N, ‖gram S lam m n‖ ≤ D) :
    LargeSieve S lam N (D * ((N / q : ℕ) : ℝ)) := by sorry
