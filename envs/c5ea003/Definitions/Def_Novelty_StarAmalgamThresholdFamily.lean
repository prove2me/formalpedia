-- Prove2me | Definitions.Def_Novelty_StarAmalgamThresholdFamily
-- name    : Novelty_StarAmalgamThresholdFamily
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:42:18.853052+00:00
-- url     : https://prove2.me/theorems/71a97a71-2e5d-4780-b7cb-8fd7c4f9c21f
-- title:
--   Aether Catalog definitions — Novelty_StarAmalgamThresholdFamily
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.StarAmalgamThresholdFamily`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/StarAmalgamThresholdFamily.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_IndependenceRatioChromatic
import Definitions.Def_Novelty_OneSumEqualityAnalysis
import Definitions.Def_Novelty_OneSumStarAmalgam

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

namespace SimpleGraph

namespace StarFamily

variable {m : ℕ}

/-- Adjacency of the `m`-fold amalgam of `K₈ - e`: blocks of seven vertices, each block
completed to a `K₈` by the cut vertex `0`, which misses the first vertex of each block. -/
def starAdj (m : ℕ) (x y : Fin (7 * m + 1)) : Prop :=
  x ≠ y ∧
    ((1 ≤ x.val ∧ 1 ≤ y.val ∧ (x.val - 1) / 7 = (y.val - 1) / 7) ∨
      (x.val = 0 ∧ 1 ≤ y.val ∧ (y.val - 1) % 7 ≠ 0) ∨
      (y.val = 0 ∧ 1 ≤ x.val ∧ (x.val - 1) % 7 ≠ 0))

/-- The `m`-fold amalgam of `K₈` minus an edge. -/
def StarK8 (m : ℕ) : SimpleGraph (Fin (7 * m + 1)) where
  Adj := starAdj m
  symm := by
    rintro x y ⟨hne, hc | hc | hc⟩
    · exact ⟨hne.symm, Or.inl ⟨hc.2.1, hc.1, hc.2.2.symm⟩⟩
    · exact ⟨hne.symm, Or.inr (Or.inr ⟨hc.1, hc.2.1, hc.2.2⟩)⟩
    · exact ⟨hne.symm, Or.inr (Or.inl ⟨hc.1, hc.2.1, hc.2.2⟩)⟩
  loopless := ⟨fun _ hx => hx.1 rfl⟩




/-- The extremal independent set: the cut vertex together with the first vertex of each block. -/
def maxIndep (m : ℕ) : Finset (Fin (7 * m + 1)) :=
  insert 0 ((Finset.univ : Finset (Fin m)).image
    (fun b => (⟨7 * b.val + 1, by have := b.isLt; omega⟩ : Fin (7 * m + 1))))








section StarSum

variable (m)

/-- The `b`-th side: the cut vertex together with the `b`-th block. -/
def side (b : Fin m) : Set (Fin (7 * m + 1)) :=
  {x | x.val = 0 ∨ (1 ≤ x.val ∧ (x.val - 1) / 7 = b.val)}

/-- The `b`-th part: the edges of the amalgam inside the `b`-th side. -/
def part (b : Fin m) : SimpleGraph (Fin (7 * m + 1)) where
  Adj x y := (StarK8 m).Adj x y ∧ x ∈ side m b ∧ y ∈ side m b
  symm := by
    rintro x y ⟨hadj, hx, hy⟩
    exact ⟨hadj.symm, hy, hx⟩
  loopless := ⟨fun _ hx => hx.1.ne rfl⟩

variable {m}



instance decidablePredSide (b : Fin m) : DecidablePred (· ∈ side m b) := by
  intro x
  unfold side
  infer_instance



/-- Each side carries an independent pair (the cut vertex and the first vertex of the block),
i.e. relative density exactly `1/4 = 2/8`. -/
def sideIndep (b : Fin m) : Finset (Fin (7 * m + 1)) :=
  {0, ⟨7 * b.val + 1, by have := b.isLt; omega⟩}







end StarSum

end StarFamily

end SimpleGraph


