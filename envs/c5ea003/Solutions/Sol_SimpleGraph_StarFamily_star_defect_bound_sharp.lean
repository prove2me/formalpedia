-- Prove2me | solution 1 for SimpleGraph.StarFamily.star_defect_bound_sharp
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:30:52.797292+00:00
-- url     : https://prove2.me/submissions/f44a8d09-e8ce-4276-86d2-158e1b6a9996

-- Sol generated from Novelty/StarAmalgamThresholdFamily.lean
import Mathlib
import Definitions.Def_Novelty_IndependenceRatioChromatic
import Definitions.Def_Novelty_OneSumEqualityAnalysis
import Definitions.Def_Novelty_OneSumStarAmalgam
import Definitions.Def_Novelty_StarAmalgamThresholdFamily
import Theorems.Thm_SimpleGraph_IsStarSum_indepRatio_ge_of_sides
import Theorems.Thm_SimpleGraph_StarFamily_card_le_of_indepSet
import Theorems.Thm_SimpleGraph_StarFamily_maxIndep_card
import Theorems.Thm_SimpleGraph_StarFamily_maxIndep_isIndepSet
import Theorems.Thm_SimpleGraph_StarFamily_sideIndep_card
import Theorems.Thm_SimpleGraph_StarFamily_sideIndep_isIndepSet
import Theorems.Thm_SimpleGraph_StarFamily_sideIndep_subset
import Theorems.Thm_SimpleGraph_StarFamily_side_card
import Theorems.Thm_SimpleGraph_StarFamily_star_isStarSum

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









/-- **The independence number of the `m`-fold amalgam is exactly `m + 1`.** -/
theorem starIndepNum : (StarK8 m).indepNum = m + 1 := by
  classical
  refine le_antisymm ?_ ?_
  · obtain ⟨S, hS, hcard⟩ := (StarK8 m).exists_isNIndepSet_indepNum
    exact hcard ▸ card_le_of_indepSet hS
  · have := maxIndep_isIndepSet (m := m) |>.card_le_indepNum
    rwa [maxIndep_card] at this

/-- **The independence ratio of the `m`-fold amalgam.** -/
theorem starIndepRatio : (StarK8 m).indepRatio = ((m : ℚ) + 1) / (7 * (m : ℚ) + 1) := by
  rw [SimpleGraph.indepRatio, starIndepNum]
  simp only [Fintype.card_fin]
  push_cast
  ring





variable (m)



variable {m}











/-- The hypotheses of the companion bound are met with `r = 1/4`: the sides have `8` vertices
and carry independent sets of size `2`, and the sides cover the amalgam with the correct
multiplicity. -/
theorem side_cover [NeZero m] :
    ((Fintype.card (Fin (7 * m + 1)) : ℚ)) + ((Fintype.card (Fin m) - 1 : ℕ) : ℚ)
      = ∑ b : Fin m, ((Finset.univ.filter (· ∈ side m b)).card : ℚ) := by
  classical
  have hm : 1 ≤ m := Nat.one_le_iff_ne_zero.2 (NeZero.ne m)
  simp only [side_card, Fintype.card_fin, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have : ((m - 1 : ℕ) : ℚ) = (m : ℚ) - 1 := by
    have : (1 : ℕ) ≤ m := hm
    push_cast [Nat.cast_sub this]
    ring
  rw [this]
  push_cast
  ring





open SimpleGraph in
theorem solution[NeZero m] :
    (1 : ℚ) / 4 - ((Fintype.card (Fin m) - 1 : ℕ) : ℚ) * (1 - (1 : ℚ) / 4)
        / (Fintype.card (Fin (7 * m + 1)) : ℚ) ≤ (StarK8 m).indepRatio ∧
      (StarK8 m).indepRatio
        = (1 : ℚ) / 4 - ((Fintype.card (Fin m) - 1 : ℕ) : ℚ) * (1 - (1 : ℚ) / 4)
            / (Fintype.card (Fin (7 * m + 1)) : ℚ) := by
  classical
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hvalue : (StarK8 m).indepRatio
      = (1 : ℚ) / 4 - ((Fintype.card (Fin m) - 1 : ℕ) : ℚ) * (1 - (1 : ℚ) / 4)
          / (Fintype.card (Fin (7 * m + 1)) : ℚ) := by
    rw [starIndepRatio]
    simp only [Fintype.card_fin]
    have hcast : ((m - 1 : ℕ) : ℚ) = (m : ℚ) - 1 := by
      have h1 : (1 : ℕ) ≤ m := hm
      push_cast [Nat.cast_sub h1]
      ring
    rw [hcast]
    have h7 : (7 : ℚ) * (m : ℚ) + 1 ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  refine ⟨?_, hvalue⟩
  refine star_isStarSum.indepRatio_ge_of_sides (s := fun b => sideIndep b)
    (fun b => sideIndep_subset b) (fun b => sideIndep_isIndepSet b) (r := (1 : ℚ) / 4)
    (fun b => ?_) ?_ (by simp)
  · rw [side_card b, sideIndep_card b]
    norm_num
  · exact side_cover
