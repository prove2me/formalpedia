-- Prove2me | solution 1 for SimpleGraph.StarFamily.card_le_of_indepSet
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:25:18.505808+00:00
-- url     : https://prove2.me/submissions/678f3e89-2f60-444f-bc93-3c318491d83b

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

/-- Two distinct vertices in the same block are adjacent. -/
theorem adj_of_same_block {x y : Fin (7 * m + 1)} (hx : 1 ≤ x.val) (hy : 1 ≤ y.val)
    (hb : (x.val - 1) / 7 = (y.val - 1) / 7) (hne : x ≠ y) : (StarK8 m).Adj x y :=
  ⟨hne, Or.inl ⟨hx, hy, hb⟩⟩











variable (m)



variable {m}
















open SimpleGraph in
theorem solution{S : Finset (Fin (7 * m + 1))} (hS : (StarK8 m).IsIndepSet ↑S) :
    S.card ≤ m + 1 := by
  classical
  have hmap : ∀ x ∈ S.erase 0, (x.val - 1) / 7 ∈ Finset.range m := by
    intro x hx
    have hx0 : x ≠ 0 := Finset.ne_of_mem_erase hx
    have hv : 1 ≤ x.val := by
      by_contra hcon
      exact hx0 ((val_eq_zero_iff x).1 (by omega))
    have hlt := x.isLt
    simp only [Finset.mem_range]
    omega
  have hinj : Set.InjOn (fun x : Fin (7 * m + 1) => (x.val - 1) / 7) (S.erase 0) := by
    intro x hx y hy hxy
    simp only [Finset.coe_erase, Set.mem_diff, Finset.mem_coe, Set.mem_singleton_iff] at hx hy
    by_contra hne
    have hxv : 1 ≤ x.val := by
      by_contra hcon
      exact hx.2 ((val_eq_zero_iff x).1 (by omega))
    have hyv : 1 ≤ y.val := by
      by_contra hcon
      exact hy.2 ((val_eq_zero_iff y).1 (by omega))
    exact hS (Finset.mem_coe.2 hx.1) (Finset.mem_coe.2 hy.1) hne
      (adj_of_same_block hxv hyv hxy hne)
  have hcard := Finset.card_le_card_of_injOn (fun x : Fin (7 * m + 1) => (x.val - 1) / 7)
    (fun x hx => Finset.mem_coe.2 (hmap x (Finset.mem_coe.1 hx))) hinj
  rw [Finset.card_range] at hcard
  have hle : S.card ≤ (S.erase 0).card + 1 := by
    by_cases h0 : (0 : Fin (7 * m + 1)) ∈ S
    · rw [Finset.card_erase_of_mem h0]
      have : 1 ≤ S.card := Finset.card_pos.2 ⟨0, h0⟩
      omega
    · rw [Finset.erase_eq_of_notMem h0]; omega
  omega
