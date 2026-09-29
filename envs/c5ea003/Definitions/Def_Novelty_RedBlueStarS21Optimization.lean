-- Prove2me | Definitions.Def_Novelty_RedBlueStarS21Optimization
-- name    : Novelty_RedBlueStarS21Optimization
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:38:57.813468+00:00
-- url     : https://prove2.me/theorems/a77440da-ac1d-4a65-bcb2-46304bc31260
-- title:
--   Aether Catalog definitions — Novelty_RedBlueStarS21Optimization
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.RedBlueStarS21Optimization`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/RedBlueStarS21Optimization.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_RedBlueStarS21Profile
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The star functional `f(d) = d²(1 − d)` and the realizability gap for `S_{2,1}`

The asymptotic semi-induced `S_{2,1}` density of a graph is the average over vertices of the
*star functional* `f(d) = d² (1 − d)`, where `d` is a vertex's local neighbour-density, while
the edge density is the average of `d`.  This file proves the shape of `f` and exposes the
*realizability gap* that makes the extremal problem nontrivial.

Two facts together explain why the true minimum profile is hard:

* `starFunctional_nonneg` / `starFunctional_le` : `f` is a bump, `0 ≤ f(d) ≤ 4/27` on `[0,1]`,
  with the maximum `4/27` at `d = 2/3`.
* `relaxed_infimum_zero` : if degrees were an *unconstrained* probability law with mean `β`,
  the average of `f` could be pushed to `0` for **every** `β ∈ [0,1]` (put mass `β` at `d = 1`
  and mass `1 − β` at `d = 0`).  Thus the mean constraint alone never forces a positive
  minimum — the genuine positivity comes solely from *graph realizability* (a degree law
  concentrated at `{0,1}` is not graphical at intermediate density).

The construction profile `minProfile t = t²(1 − t)` is exactly `f` evaluated at the parameter
`t` (`minProfile_eq_starFunctional`), and on the construction's honest range its value stays
below the bump maximum (`construction_profile_le_max`).

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): The semi-induced minimum is forced to be positive at intermediate
  density by the *mean* edge-density constraint alone.
Experiment (Experimenter): Disproved the mean-only hypothesis: the two-point law at `{0,1}`
  with mass `β` at `1` has mean `β` and `f`-average `0` for every `β` (`relaxed_infimum_zero`).
  Proved `starFunctional_nonneg`, `starFunctional_le` (bump `≤ 4/27`), `starFunctional_max`.
Analysis (Analyst): The positivity of the genuine graph minimum is therefore *purely* a
  realizability phenomenon: at edge density `1/2` no graph can have almost every vertex of
  neighbour-density `0` or `1` (universal vertices force everyone's degree up), so the
  `f`-average stays bounded away from `0`.  This is exactly why `minProfile 1 = 0` at
  `β = 1/2` is unattainable and the headline profile breaks at the top of its range.
Critique (Critic): `relaxed_infimum_zero` must be a genuine identity, not vacuous — verified it
  produces mean `β` and average `0` simultaneously via `ring`.  `starFunctional_le` is an
  `nlinarith` certificate on `(3d − 2)²`, not a `norm_num` evaluation, so the bump bound is
  load-bearing.
Synthesis (PI): The clean separation — `f` bounded, mean-relaxation zero — pinpoints the open
  difficulty as a realizability lower bound, recorded in `FUTURE_DIRECTIONS.md`.
-/

namespace RedBlueStarS21

open Set

/-- The per-vertex *star functional* `f(d) = d²(1 − d)`, whose vertex-average is the
asymptotic semi-induced `S_{2,1}` density. -/
noncomputable def starFunctional (d : ℝ) : ℝ := d ^ 2 * (1 - d)








end RedBlueStarS21


