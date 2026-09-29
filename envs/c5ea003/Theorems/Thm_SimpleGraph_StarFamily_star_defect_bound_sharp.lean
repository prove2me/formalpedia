-- Prove2me | Theorems.Thm_SimpleGraph_StarFamily_star_defect_bound_sharp
-- name    : SimpleGraph.StarFamily.star_defect_bound_sharp
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:33:48.393487+00:00
-- url     : https://prove2.me/theorems/19f7a5ad-6a95-4757-90ce-5f07c14a767d
-- title:
--   Capstone: the `m`-fold defect bound is sharp for every `m`.
-- statement:
--   **Capstone: the `m`-fold defect bound is sharp for every `m`.**  The general star-amalgam
--   bound of `Novelty.OneSumStarAmalgam`, instantiated at the threshold density `r = 1/4`, is both
--   *valid* and *attained* by the family `StarK8 m`.
--
--   ```lean
--   theorem SimpleGraph.StarFamily.star_defect_bound_sharp[NeZero m] :
--       (1 : ℚ) / 4 - ((Fintype.card (Fin m) - 1 : ℕ) : ℚ) * (1 - (1 : ℚ) / 4)
--           / (Fintype.card (Fin (7 * m + 1)) : ℚ) ≤ (StarK8 m).indepRatio ∧
--         (StarK8 m).indepRatio
--           = (1 : ℚ) / 4 - ((Fintype.card (Fin m) - 1 : ℕ) : ℚ) * (1 - (1 : ℚ) / 4)
--               / (Fintype.card (Fin (7 * m + 1)) : ℚ) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/StarAmalgamThresholdFamily.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/StarAmalgamThresholdFamily.lean#L415

-- Thm stub generated from Novelty/StarAmalgamThresholdFamily.lean
import Mathlib
import Definitions.Def_Novelty_IndependenceRatioChromatic
import Definitions.Def_Novelty_OneSumEqualityAnalysis
import Definitions.Def_Novelty_OneSumStarAmalgam
import Definitions.Def_Novelty_StarAmalgamThresholdFamily

/-!
# The threshold family: `m`-fold amalgams of `K₈ - e` and the collapse of the ratio to `1/7`

`Novelty.OneSumStarAmalgam` proved that an `m`-fold star amalgam obeys the sharp bound
`i(G) ≥ r - (m-1)(1-r)/n` when all sides carry independent sets of relative density `r`.
This file exhibits the extremal family for `r = 1/4`, thereby showing that the defect term is
optimal for **every** `m`, and that iterated 1-sums of graphs sitting exactly on the
threshold `i = 1/4` drive the independence ratio all the way down to `1/7`.

`StarK8 m` is the amalgam of `m` copies of `K₈` minus an edge, all glued at one vertex `0`:
the vertex set is `Fin (7m+1)`, block `b` is `{7b+1, …, 7b+7}`, block `b` together with `0`
spans a `K₈` minus the edge `{0, 7b+1}`.

Main results.

* `SimpleGraph.StarFamily.starIndepNum` — `α(StarK8 m) = m + 1`;
* `SimpleGraph.StarFamily.starIndepRatio` — `i(StarK8 m) = (m+1)/(7m+1)`;
* `SimpleGraph.StarFamily.star_isStarSum` — `StarK8 m` really is an `m`-fold star amalgam;
* `SimpleGraph.StarFamily.side_card` and `SimpleGraph.StarFamily.side_indepSet_card` — every
  side has `8` vertices and carries an independent pair, i.e. relative density exactly `1/4`;
* `SimpleGraph.StarFamily.starIndepRatio_eq_defect_bound` — the `m`-fold defect bound of the
  companion file is attained with equality for every `m`;
* `SimpleGraph.StarFamily.starIndepRatio_sub_seventh` — the exact identity
  `i(StarK8 m) - 1/7 = 6/(7(7m+1))`, whence
* `SimpleGraph.StarFamily.exists_indepRatio_lt` — for every `ε > 0` some amalgam of threshold
  graphs has independence ratio below `1/7 + ε`, and
  `SimpleGraph.StarFamily.starIndepRatio_lt_quarter` — every amalgam with `m ≥ 2` parts is
  already below `1/4`.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): iterating the two-part counterexample should be *cumulative*, not
merely repeatable: with `m` parts the ratio should be `(m+1)/(7m+1)`, decreasing to `1/7`.
Experiment (Experimenter): `α = m + 1` because an independent set meets each block in at most
one vertex (blocks are cliques) and may in addition contain the cut vertex; the extremal set
is `{0} ∪ {7b+1 : b < m}`, the cut vertex together with the non-neighbour in each block.
Numerically: `m = 1 : 2/8 = 1/4`, `m = 2 : 3/15 = 1/5`, `m = 3 : 4/22 = 2/11`,
`m = 10 : 11/71`, limit `1/7 ≈ 0.1428…`.
Analysis (Analyst): the identity `i - 1/7 = 6/(7(7m+1))` shows the convergence is exactly of
order `1/n`, i.e. the entire deficiency is carried by the single shared vertex.
Critique (Critic): `1/7` is *not* attained; the family is strictly above it for every finite
`m`, so the statement is an infimum statement, formalised as an explicit `ε`-approximation
rather than as an unattained minimum.
Synthesis (PI): "threshold" hypotheses of the form `i ≥ c` are never closed under
amalgamation; the only stable formulation is the colouring one.
-- !-- end Lab Notes -- !--
-/

open Finset

open SimpleGraph

open StarFamily

variable {m : ℕ}















variable (m)



variable {m}

theorem SimpleGraph.StarFamily.star_defect_bound_sharp[NeZero m] :
    (1 : ℚ) / 4 - ((Fintype.card (Fin m) - 1 : ℕ) : ℚ) * (1 - (1 : ℚ) / 4)
        / (Fintype.card (Fin (7 * m + 1)) : ℚ) ≤ (StarK8 m).indepRatio ∧
      (StarK8 m).indepRatio
        = (1 : ℚ) / 4 - ((Fintype.card (Fin m) - 1 : ℕ) : ℚ) * (1 - (1 : ℚ) / 4)
            / (Fintype.card (Fin (7 * m + 1)) : ℚ) := by sorry
