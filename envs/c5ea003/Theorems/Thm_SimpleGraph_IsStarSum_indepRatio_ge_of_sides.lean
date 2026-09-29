-- Prove2me | Theorems.Thm_SimpleGraph_IsStarSum_indepRatio_ge_of_sides
-- name    : SimpleGraph.IsStarSum.indepRatio_ge_of_sides
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:33:19.775555+00:00
-- url     : https://prove2.me/theorems/54e25a63-96fa-4948-8c95-ff6153ec4d0c
-- title:
--   The sharp ratio bound for an `m`-fold star amalgam.
-- statement:
--   **The sharp ratio bound for an `m`-fold star amalgam.**  If each side carries an
--   independent set of relative density at least `r`, then `i(G) ≥ r - (m-1)(1-r)/n`.
--
--   ```lean
--   theorem SimpleGraph.IsStarSum.indepRatio_ge_of_sides[Nonempty ι] [∀ i, DecidablePred (· ∈ A i)]
--       {s : ι → Finset V} (hs : ∀ i, ↑(s i) ⊆ A i) (hi : ∀ i, (H i).IsIndepSet ↑(s i))
--       {r : ℚ}
--       (hr : ∀ i, r * ((Finset.univ.filter (· ∈ A i)).card : ℚ) ≤ ((s i).card : ℚ))
--       (hcover : (Fintype.card V : ℚ) + (Fintype.card ι - 1 : ℕ)
--         = ∑ i, ((Finset.univ.filter (· ∈ A i)).card : ℚ))
--       (hpos : 0 < Fintype.card V) :
--       r - ((Fintype.card ι - 1 : ℕ) : ℚ) * (1 - r) / (Fintype.card V : ℚ) ≤ G.indepRatio := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/OneSumStarAmalgam.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/OneSumStarAmalgam.lean#L275

-- Thm stub generated from Novelty/OneSumStarAmalgam.lean
import Mathlib
import Definitions.Def_Novelty_IndependenceRatioChromatic
import Definitions.Def_Novelty_OneSumEqualityAnalysis
import Definitions.Def_Novelty_OneSumStarAmalgam

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

open SimpleGraph

variable {V ι : Type*}


open IsStarSum

variable {G : SimpleGraph V} {H : ι → SimpleGraph V} {A : ι → Set V} {v : V}
variable (h : IsStarSum G H A v)
include h







variable [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]

theorem SimpleGraph.IsStarSum.indepRatio_ge_of_sides[Nonempty ι] [∀ i, DecidablePred (· ∈ A i)]
    {s : ι → Finset V} (hs : ∀ i, ↑(s i) ⊆ A i) (hi : ∀ i, (H i).IsIndepSet ↑(s i))
    {r : ℚ}
    (hr : ∀ i, r * ((Finset.univ.filter (· ∈ A i)).card : ℚ) ≤ ((s i).card : ℚ))
    (hcover : (Fintype.card V : ℚ) + (Fintype.card ι - 1 : ℕ)
      = ∑ i, ((Finset.univ.filter (· ∈ A i)).card : ℚ))
    (hpos : 0 < Fintype.card V) :
    r - ((Fintype.card ι - 1 : ℕ) : ℚ) * (1 - r) / (Fintype.card V : ℚ) ≤ G.indepRatio := by sorry
