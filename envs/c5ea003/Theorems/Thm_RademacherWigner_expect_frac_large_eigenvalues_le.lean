-- Prove2me | Theorems.Thm_RademacherWigner_expect_frac_large_eigenvalues_le
-- name    : RademacherWigner.expect_frac_large_eigenvalues_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-15T02:47:42.584007+00:00
-- url     : https://prove2.me/theorems/326cc804-0e66-46ba-97de-87b7708d715f
-- title:
--   Uniform tail bound for the empirical spectral distribution.
-- statement:
--   **Uniform tail bound for the empirical spectral distribution.**  For every order
--   `k ≥ 1` and every threshold `t > 0`, the expected fraction of eigenvalues of `W/√N`
--   of modulus at least `t` is at most `(k+1)^(2k) / t^(2k)`, a bound that does not
--   depend on the dimension `N`.
--
--   ```lean
--   theorem RademacherWigner.expect_frac_large_eigenvalues_le{k : ℕ} (hk : 1 ≤ k) (hN : 0 < N) {t : ℝ}
--       (ht : 0 < t) :
--       expect (fun g : Config N =>
--           (((univ.filter fun i =>
--               t ≤ |(W_isHermitian g).eigenvalues i| / Real.sqrt (N : ℝ)).card : ℝ) / (N : ℝ)))
--         ≤ ((k : ℝ) + 1) ^ (2 * k) / t ^ (2 * k) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/WignerBulkTightness.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/WignerBulkTightness.lean#L89

-- Thm stub generated from Probability/WignerBulkTightness.lean
import Mathlib
import Definitions.Def_Probability_WignerMomentGrowth
import Definitions.Def_Probability_WignerRademacherEnsemble
import Theorems.Thm_RademacherWigner_W_isHermitian
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# Tightness of the empirical spectral distribution

`Probability.WignerSpectralEdge` bounds the probability that *some* eigenvalue of
`W/√N` is large.  This file records the complementary — and for the semicircle law
more fundamental — statement about the *bulk*: the empirical spectral distribution
(ESD) of `W/√N` puts almost no mass far from the origin, uniformly in the dimension.

* `WignerBridge.frac_large_eigenvalues_le` is deterministic and holds for an
  arbitrary real symmetric matrix: the fraction of eigenvalues of `A/√N` of modulus
  at least `t` is at most `(2k)`-th normalised moment divided by `t^(2k)` — Markov's
  inequality applied to the ESD itself rather than to the ensemble.

* `RademacherWigner.expect_frac_large_eigenvalues_le` combines this with the uniform
  moment bound `expect_normalizedMoment_two_mul_le` to give, for every `k ≥ 1`,

    `E [ #{ i : |λᵢ|/√N ≥ t } / N ] ≤ (k+1)^(2k) / t^(2k)`,

  a bound independent of `N`.

* `RademacherWigner.esd_tight` is the resulting **tightness** statement: for every
  `ε > 0` there is a threshold `t` such that, in *every* dimension, the expected
  fraction of eigenvalues of `W/√N` outside `[-t, t]` is at most `ε`.  Tightness is
  exactly the compactness hypothesis under which convergence of all moments upgrades
  to weak convergence of the ESD, i.e. it is the missing analytic half of the moment
  method (Conjecture 4 of `FUTURE_DIRECTIONS.md`).
-/

open Matrix BigOperators Finset

open WignerBridge



open RademacherWigner

variable {N : ℕ}

theorem RademacherWigner.expect_frac_large_eigenvalues_le{k : ℕ} (hk : 1 ≤ k) (hN : 0 < N) {t : ℝ}
    (ht : 0 < t) :
    expect (fun g : Config N =>
        (((univ.filter fun i =>
            t ≤ |(W_isHermitian g).eigenvalues i| / Real.sqrt (N : ℝ)).card : ℝ) / (N : ℝ)))
      ≤ ((k : ℝ) + 1) ^ (2 * k) / t ^ (2 * k) := by sorry
