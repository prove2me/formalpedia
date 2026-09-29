-- Prove2me | Definitions.Def_Novelty_RedBlueStarS21Profile
-- name    : Novelty_RedBlueStarS21Profile
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:38:22.305458+00:00
-- url     : https://prove2.me/theorems/8737b523-d58c-4063-a65e-26acfbe2d3fc
-- title:
--   Aether Catalog definitions — Novelty_RedBlueStarS21Profile
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.RedBlueStarS21Profile`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/RedBlueStarS21Profile.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The lower semi-inducibility profile of the red-blue star `S_{2,1}`: parametrization and a refutation

A red-blue star `S_{2,1}` is the 4-vertex coloured pattern with a centre joined to two
*red* (present) leaves and one *blue* (absent) leaf; a **semi-induced** copy fixes only the
three centre-leaf pairs and leaves the three leaf-leaf pairs free.  Asymptotically the
semi-induced `S_{2,1}` density of a graph is the per-vertex *star functional*
`f(d) = d² (1 − d)` averaged over the vertices, where `d` is the local neighbour-density,
while the edge density is the average of `d`.

The proposed *one-parameter three-class complement-split profile* claims:

> for every edge density `β ∈ [0,1]`, letting `t ∈ [0,1]` be the unique solution of
> `β = t (1 − t/2)`, the minimum semi-induced `S_{2,1}` density equals `t² (1 − t)`.

This file isolates the **parametrization map** `edgeDensity t = t (1 − t/2)` and the
**profile map** `minProfile t = t² (1 − t)`, proves their genuine structural shape, and
exposes a fatal range obstruction: `edgeDensity` is a strictly increasing bijection of
`[0,1]` onto `[0, 1/2]` — it never exceeds `1/2`.  Consequently the parameter `t`
*does not exist* for any `β > 1/2`, so the universal "for every `β ∈ [0,1]`" statement is
ill-posed above one half.  We turn this into a formal refutation
(`claim_illposed_above_half`, `refutation_three_quarters`).

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): The construction's edge density `β(t) = t(1 − t/2)` and its
  semi-induced density `p(t) = t²(1 − t)` together trace the *exact* lower profile over the
  whole interval `β ∈ [0,1]`.
Experiment (Experimenter): Computed `β(t)` on a grid (`ComputationalEvidence.md`): the values
  rise monotonically from `0` to `0.5` and stop — `β(1) = 1/2`.  Formalized
  `edgeDensity_strictMonoOn`, `edgeDensity_le_half`, `edgeDensity_eq_half_iff`, and the IVT
  existence/uniqueness of `t` on the *true* range `[0, 1/2]` (`exists_unique_param`).
Analysis (Analyst): `1/2 − β(t) = (1 − t)²/2 ≥ 0`, so `β` is capped at `1/2`; the cap is the
  algebraic shadow of the quadratic.  Hence the parameter `t` exists exactly on `[0,1/2]`
  and the "for every `β ∈ [0,1]`" quantifier overreaches: there is no `t` for `β = 3/4`.
  Separately, the per-vertex *relaxation* of the minimum is `0` for every `β`
  (two-point degree law at `{0,1}`), so the genuine positivity of the minimum is forced by
  graph realizability, not by the mean — see `RedBlueStarS21Optimization.lean`.
Critique (Critic): The closed evaluations `edgeDensity 1 = 1/2` alone would be norm_num-only.
  The load-bearing results are the ordered-field inequality `edgeDensity_le_half`
  (an `nlinarith` certificate on `(1−t)²`), the strict monotonicity, the IVT-based
  `exists_unique_param`, and the refutation `claim_illposed_above_half`, each of which carries
  real content beyond evaluation.
Synthesis (PI): The profile is honest only on `β ∈ [0, 1/2]`; the half-range `[1/2,1]` must be
  reached by the *complement* pattern `S_{1,2}` (red/blue swapped), not by this same formula —
  recorded as a corrected conjecture in `FUTURE_DIRECTIONS.md`.
-/

namespace RedBlueStarS21

open Set

/-- Edge density of the one-parameter complement-split construction:
`β(t) = t (1 − t/2)`. -/
noncomputable def edgeDensity (t : ℝ) : ℝ := t * (1 - t / 2)

/-- The claimed minimum semi-induced `S_{2,1}` density along the construction:
`p(t) = t² (1 − t)`. -/
noncomputable def minProfile (t : ℝ) : ℝ := t ^ 2 * (1 - t)













end RedBlueStarS21


