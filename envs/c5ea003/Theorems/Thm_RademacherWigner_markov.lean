-- Prove2me | Theorems.Thm_RademacherWigner_markov
-- name    : RademacherWigner.markov
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:04:31.324334+00:00
-- url     : https://prove2.me/theorems/c3ddbcf8-c040-402c-90fb-d7a9c4d14cb7
-- title:
--   Markov's inequality for the uniform ensemble.
-- statement:
--   **Markov's inequality** for the uniform ensemble.
--
--   ```lean
--   theorem RademacherWigner.markov(f : Config N → ℝ) (hf : ∀ g, 0 ≤ f g) {c : ℝ} (hc : 0 < c) :
--       prob (Finset.univ.filter fun g : Config N => c ≤ f g) ≤ expect f / c := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/WignerSpectralEdge.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/WignerSpectralEdge.lean#L39

-- Thm stub generated from Probability/WignerSpectralEdge.lean
import Mathlib
import Definitions.Def_Probability_WignerMomentGrowth
import Definitions.Def_Probability_WignerRademacherEnsemble
import Definitions.Def_Probability_WignerSpectralEdge
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

theorem RademacherWigner.markov(f : Config N → ℝ) (hf : ∀ g, 0 ≤ f g) {c : ℝ} (hc : 0 < c) :
    prob (Finset.univ.filter fun g : Config N => c ≤ f g) ≤ expect f / c := by sorry
