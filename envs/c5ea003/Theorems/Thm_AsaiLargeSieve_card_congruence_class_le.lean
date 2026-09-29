-- Prove2me | Theorems.Thm_AsaiLargeSieve_card_congruence_class_le
-- name    : AsaiLargeSieve.card_congruence_class_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T14:59:34.614379+00:00
-- url     : https://prove2.me/theorems/0c8d9c29-8fc3-4d36-87e9-d25cbd9e0b13
-- title:
--   A residue class modulo `q` meets `[0, N)` in at most `N / q + 1` points.
-- statement:
--   A residue class modulo `q` meets `[0, N)` in at most `N / q + 1` points.
--
--   ```lean
--   theorem AsaiLargeSieve.card_congruence_class_le(N q m : ℕ) :
--       (((Finset.range N).filter (fun n => m ≡ n [MOD q])).card : ℕ) ≤ N / q + 1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/AsaiMomentApplications.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/AsaiMomentApplications.lean#L63

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

theorem AsaiLargeSieve.card_congruence_class_le(N q m : ℕ) :
    (((Finset.range N).filter (fun n => m ≡ n [MOD q])).card : ℕ) ≤ N / q + 1 := by sorry
