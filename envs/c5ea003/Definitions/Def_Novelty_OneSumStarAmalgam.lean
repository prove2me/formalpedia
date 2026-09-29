-- Prove2me | Definitions.Def_Novelty_OneSumStarAmalgam
-- name    : Novelty_OneSumStarAmalgam
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:35:02.64059+00:00
-- url     : https://prove2.me/theorems/08f61b73-f376-4631-ad2f-9f65e003a41e
-- title:
--   Aether Catalog definitions — Novelty_OneSumStarAmalgam
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.OneSumStarAmalgam`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/OneSumStarAmalgam.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_IndependenceRatioChromatic
import Definitions.Def_Novelty_OneSumEqualityAnalysis

/-!
# Star amalgams: iterated 1-sums at a common cut vertex

`Novelty.OneSumEqualityAnalysis` analysed a single 1-sum `G = G₁ ⊕_v G₂`.  Iterating the
construction at one *fixed* cut vertex gives the **star amalgam** of a finite family
`H : ι → SimpleGraph V`: the parts pairwise meet exactly in `{v}` and cover the vertex set.
This file proves the two structural theorems of the previous file in the `m`-fold setting and
shows how the defect grows.

Main results.

* `SimpleGraph.IsStarSum.colorable` — **colourability is closed under star amalgams**: if every
  part is `k`-colourable, so is the amalgam.  Each part is recoloured by the transposition
  matching its colour at the cut vertex with the colour of a reference part.
* `SimpleGraph.IsStarSum.sum_card_le_indepNum_add` — **the independence defect of an `m`-fold
  amalgam is exactly `m - 1`**: for independent sets `sᵢ ⊆ Aᵢ` of the parts,
  `∑ᵢ |sᵢ| ≤ α(G) + (m - 1)`.
* `SimpleGraph.IsStarSum.indepRatio_ge_of_sides` — the resulting sharp bound on the
  independence ratio: if each side carries an independent set of relative density `r`, then
  `i(G) ≥ r - (m-1)(1-r)/n`.

The companion file `Novelty.StarAmalgamThresholdFamily` shows that this bound is attained for
*every* `m`, by an `m`-fold amalgam of copies of `K₈` minus an edge; letting `m → ∞` drives the
independence ratio of an amalgam of threshold graphs (`i = 1/4`) down to `1/7`.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): the single-cut defect `1` should accumulate linearly, giving
`m - 1` for an `m`-fold amalgam, and the colouring closure should survive verbatim because a
star amalgam only ever forces *one* colour to be matched per part.
Experiment (Experimenter): the colouring construction chooses, for each vertex `x ≠ v`, the
unique index whose side contains `x` (uniqueness is exactly `Aᵢ ∩ Aⱼ = {v}`), and applies
`Equiv.swap (C i₀ v) (C i v)`.  The independence bound splits on whether *some* part avoids the
cut vertex: if all parts contain it, the plain union works and loses `m - 1`; otherwise erasing
`v` everywhere loses at most `m - 1` as well, because the part avoiding `v` loses nothing.
Analysis (Analyst): both proofs are "one cut vertex at a time" arguments, i.e. the star amalgam
behaves like a tree of 1-sums with all cut vertices identified; the defect is the number of
extra copies of the cut vertex, `m - 1`.
Critique (Critic): `Nonempty ι` is load-bearing in the colouring theorem (an empty family makes
`G = ⊥`, still colourable, but the reference colour `C i₀ v` does not exist); the pairwise
condition `i ≠ j → Aᵢ ∩ Aⱼ = {v}` cannot be weakened to `⋂ᵢ Aᵢ = {v}` — two parts sharing two
vertices break both theorems.
Synthesis (PI): 1-sums act as `max` on colouring invariants and as an additive-with-defect
operation on independence; the defect is the only obstruction to closure of ratio thresholds.
-- !-- end Lab Notes -- !--
-/

open Finset

namespace SimpleGraph

variable {V ι : Type*}

/-- `G` is the **star amalgam** of the family `H` with sides `A`, all glued at the single cut
vertex `v`. -/
structure IsStarSum (G : SimpleGraph V) (H : ι → SimpleGraph V) (A : ι → Set V) (v : V) :
    Prop where
  /-- `G` is the edge-union of the parts. -/
  sup_eq : G = ⨆ i, H i
  /-- The edges of the `i`-th part live inside the `i`-th side. -/
  support : ∀ i ⦃x y⦄, (H i).Adj x y → x ∈ A i ∧ y ∈ A i
  /-- Two distinct sides meet exactly in the cut vertex. -/
  inter_eq : ∀ i j, i ≠ j → A i ∩ A j = {v}
  /-- Every side contains the cut vertex. -/
  cut_mem : ∀ i, v ∈ A i
  /-- The sides cover the vertex set. -/
  union_eq : (⋃ i, A i) = Set.univ

namespace IsStarSum

variable {G : SimpleGraph V} {H : ι → SimpleGraph V} {A : ι → Set V} {v : V}
variable (h : IsStarSum G H A v)
include h







variable [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]





section Invariants

variable [Nonempty ι]





end Invariants

end IsStarSum

end SimpleGraph


