-- Prove2me | Definitions.Def_Probability_WignerSpectralEdge
-- name    : Probability_WignerSpectralEdge
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:47:33.741699+00:00
-- url     : https://prove2.me/theorems/abe57dd2-7376-4940-8a8b-4e9aa95a29da
-- title:
--   Aether Catalog definitions — Probability_WignerSpectralEdge
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.WignerSpectralEdge`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/WignerSpectralEdge.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Probability_WignerMomentGrowth
import Definitions.Def_Probability_WignerRademacherEnsemble
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

namespace RademacherWigner

variable {N : ℕ}

/-- The uniform probability of a set of configurations. -/
noncomputable def prob (A : Finset (Config N)) : ℝ :=
  (A.card : ℝ) / (Fintype.card (Config N) : ℝ)






end RademacherWigner


