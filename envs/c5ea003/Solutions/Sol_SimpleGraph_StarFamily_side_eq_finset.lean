-- Prove2me | solution 1 for SimpleGraph.StarFamily.side_eq_finset
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:27:39.719169+00:00
-- url     : https://prove2.me/submissions/d9749aae-4153-4589-96e4-2e9e9a6f919d

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
















open SimpleGraph in
theorem solution(b : Fin m) :
    (Finset.univ.filter (· ∈ side m b))
      = insert 0 ((Finset.univ : Finset (Fin 7)).image
          (fun j => (⟨7 * b.val + 1 + j.val, by
            have := b.isLt; have := j.isLt; omega⟩ : Fin (7 * m + 1)))) := by
  classical
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_image,
    side, Set.mem_setOf_eq]
  constructor
  · rintro (hx | ⟨hx1, hx2⟩)
    · exact Or.inl ((val_eq_zero_iff x).1 hx)
    · refine Or.inr ⟨⟨x.val - 1 - 7 * b.val, by omega⟩, ?_⟩
      apply Fin.ext
      show 7 * b.val + 1 + (x.val - 1 - 7 * b.val) = x.val
      omega
  · rintro (rfl | ⟨j, rfl⟩)
    · exact Or.inl (by simp)
    · have hj := j.isLt
      refine Or.inr ⟨?_, ?_⟩
      · show 1 ≤ 7 * b.val + 1 + j.val
        omega
      · show (7 * b.val + 1 + j.val - 1) / 7 = b.val
        omega
