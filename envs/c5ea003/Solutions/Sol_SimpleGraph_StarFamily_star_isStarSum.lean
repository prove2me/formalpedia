-- Prove2me | solution 1 for SimpleGraph.StarFamily.star_isStarSum
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:29:05.187883+00:00
-- url     : https://prove2.me/submissions/010b7369-7743-480f-835c-2d9df6d92c4c

-- Sol generated from Novelty/StarAmalgamThresholdFamily.lean
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



theorem val_eq_zero_iff (x : Fin (7 * m + 1)) : x.val = 0 ↔ x = 0 := by
  constructor
  · intro h; exact Fin.ext (by simpa using h)
  · intro h; simp [h]












variable (m)



variable {m}

theorem mem_side_zero (b : Fin m) : (0 : Fin (7 * m + 1)) ∈ side m b := Or.inl (by simp)















open SimpleGraph in
theorem solution[NeZero m] : (StarK8 m).IsStarSum (part m) (side m) 0 where
  sup_eq := by
    ext x y
    simp only [SimpleGraph.iSup_adj]
    constructor
    · intro hadj
      obtain ⟨hne, hc | hc | hc⟩ := hadj
      · have hlt := x.isLt
        have hb : (x.val - 1) / 7 < m := by omega
        refine ⟨⟨(x.val - 1) / 7, hb⟩, ⟨hne, Or.inl hc⟩, Or.inr ⟨hc.1, rfl⟩,
          Or.inr ⟨hc.2.1, hc.2.2.symm⟩⟩
      · have hlt := y.isLt
        have hb : (y.val - 1) / 7 < m := by omega
        exact ⟨⟨(y.val - 1) / 7, hb⟩, ⟨hne, Or.inr (Or.inl hc)⟩, Or.inl hc.1,
          Or.inr ⟨hc.2.1, rfl⟩⟩
      · have hlt := x.isLt
        have hb : (x.val - 1) / 7 < m := by omega
        exact ⟨⟨(x.val - 1) / 7, hb⟩, ⟨hne, Or.inr (Or.inr hc)⟩, Or.inr ⟨hc.2.1, rfl⟩,
          Or.inl hc.1⟩
    · rintro ⟨b, hadj, -, -⟩
      exact hadj
  support := fun _ _ _ hxy => ⟨hxy.2.1, hxy.2.2⟩
  inter_eq := by
    intro i j hij
    ext x
    simp only [side, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hi | hi, hj | hj⟩
      · exact (val_eq_zero_iff x).1 hi
      · exact (val_eq_zero_iff x).1 hi
      · exact (val_eq_zero_iff x).1 hj
      · exact absurd (Fin.ext (hi.2.symm.trans hj.2)) hij
    · rintro rfl
      constructor
      · exact Or.inl (by simp)
      · exact Or.inl (by simp)
  cut_mem := mem_side_zero
  union_eq := by
    ext x
    simp only [Set.mem_iUnion, side, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
    by_cases hx : x.val = 0
    · exact ⟨⟨0, hm⟩, Or.inl hx⟩
    · have hlt := x.isLt
      have hb : (x.val - 1) / 7 < m := by omega
      exact ⟨⟨(x.val - 1) / 7, hb⟩, Or.inr ⟨by omega, rfl⟩⟩
