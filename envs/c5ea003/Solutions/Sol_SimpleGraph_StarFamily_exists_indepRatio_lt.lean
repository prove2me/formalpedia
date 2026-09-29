-- Prove2me | solution 1 for SimpleGraph.StarFamily.exists_indepRatio_lt
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:27:37.743978+00:00
-- url     : https://prove2.me/submissions/cfb64dc3-c151-4340-92bb-b28fd123bddc

-- Sol generated from Novelty/StarAmalgamThresholdFamily.lean
import Mathlib
import Definitions.Def_Novelty_IndependenceRatioChromatic
import Definitions.Def_Novelty_OneSumEqualityAnalysis
import Definitions.Def_Novelty_OneSumStarAmalgam
import Definitions.Def_Novelty_StarAmalgamThresholdFamily
import Theorems.Thm_SimpleGraph_StarFamily_card_le_of_indepSet
import Theorems.Thm_SimpleGraph_StarFamily_maxIndep_card
import Theorems.Thm_SimpleGraph_StarFamily_maxIndep_isIndepSet

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

/-- **The exact distance to `1/7`.**  The whole deficiency of the amalgam is carried by the
single shared vertex, and it decays like `1/n`. -/
theorem starIndepRatio_sub_seventh :
    (StarK8 m).indepRatio - (1 : ℚ) / 7 = 6 / (7 * (7 * (m : ℚ) + 1)) := by
  rw [starIndepRatio]
  have h7 : (7 : ℚ) * (m : ℚ) + 1 ≠ 0 := by positivity
  field_simp
  ring




variable (m)



variable {m}
















open SimpleGraph in
theorem solution{ε : ℚ} (hε : 0 < ε) :
    ∃ m : ℕ, (StarK8 m).indepRatio < (1 : ℚ) / 7 + ε := by
  obtain ⟨m, hm⟩ := exists_nat_gt (6 / ε)
  refine ⟨m, ?_⟩
  have hmq : (0 : ℚ) ≤ (m : ℚ) := Nat.cast_nonneg m
  have hkey := starIndepRatio_sub_seventh (m := m)
  have hpos : (0 : ℚ) < 7 * (7 * (m : ℚ) + 1) := by positivity
  have hlt : 6 / (7 * (7 * (m : ℚ) + 1)) < ε := by
    rw [div_lt_iff₀ hpos]
    have h6 : 6 / ε < (m : ℚ) := hm
    have : 6 < ε * (m : ℚ) := by
      rw [div_lt_iff₀ hε] at h6
      linarith
    nlinarith
  linarith
