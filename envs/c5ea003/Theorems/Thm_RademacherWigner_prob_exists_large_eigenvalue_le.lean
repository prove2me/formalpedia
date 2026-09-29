-- Prove2me | Theorems.Thm_RademacherWigner_prob_exists_large_eigenvalue_le
-- name    : RademacherWigner.prob_exists_large_eigenvalue_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-15T02:47:57.090184+00:00
-- url     : https://prove2.me/theorems/92d834ac-56f4-4407-9163-39764287739c
-- title:
--   Spectral-edge tail bound.
-- statement:
--   **Spectral-edge tail bound.**  For every order `k ≥ 1` and threshold `t > 0`, the
--   probability that the ensemble produces an eigenvalue of `W/√N` of modulus at least
--   `t` is at most `N (k+1)^(2k) / t^(2k)`.
--
--   ```lean
--   theorem RademacherWigner.prob_exists_large_eigenvalue_le{k : ℕ} (hk : 1 ≤ k) (hN : 0 < N) {t : ℝ}
--       (ht : 0 < t) :
--       prob (Finset.univ.filter fun g : Config N =>
--           ∃ i, t * Real.sqrt (N : ℝ) ≤ |(W_isHermitian g).eigenvalues i|)
--         ≤ (N : ℝ) * ((k : ℝ) + 1) ^ (2 * k) / t ^ (2 * k) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/WignerSpectralEdge.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/WignerSpectralEdge.lean#L71

-- Thm stub generated from Probability/WignerSpectralEdge.lean
import Mathlib
import Definitions.Def_Probability_WignerMomentGrowth
import Definitions.Def_Probability_WignerRademacherEnsemble
import Definitions.Def_Probability_WignerSpectralEdge
import Theorems.Thm_RademacherWigner_W_isHermitian
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# A quantitative spectral-edge bound at every order

`Probability.WignerMomentGrowth` bounds every even trace moment of the symmetric
Rademacher ensemble by `N^(k+1) (k+1)^(2k)`.  Because a single large eigenvalue
already forces a large `2k`-th trace moment, Markov's inequality turns that bound
into a tail estimate for the spectral radius: for every order `k` and every
threshold `t > 0`,

  `P [ some eigenvalue of W/√N has modulus ≥ t ] ≤ N (k+1)^(2k) / t^(2k)`.

This is the classical moment route to the spectral edge; the constant `(k+1)^(2k)`
is the crude spanning-tree count rather than the sharp Catalan constant `4^k`, so
the bound becomes informative for `t` of order `k`, and combined with the
deterministic lower bound `√(1 - 1/N) ≤ ‖W/√N‖` of
`Probability.WignerSemicircleCapstone` it sandwiches the spectral radius from both
sides.
-/

open Matrix BigOperators Finset

open RademacherWigner

variable {N : ℕ}

theorem RademacherWigner.prob_exists_large_eigenvalue_le{k : ℕ} (hk : 1 ≤ k) (hN : 0 < N) {t : ℝ}
    (ht : 0 < t) :
    prob (Finset.univ.filter fun g : Config N =>
        ∃ i, t * Real.sqrt (N : ℝ) ≤ |(W_isHermitian g).eigenvalues i|)
      ≤ (N : ℝ) * ((k : ℝ) + 1) ^ (2 * k) / t ^ (2 * k) := by sorry
