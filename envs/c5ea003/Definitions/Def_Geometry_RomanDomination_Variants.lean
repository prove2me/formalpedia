-- Prove2me | Definitions.Def_Geometry_RomanDomination_Variants
-- name    : Geometry_RomanDomination_Variants
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:52:51.744076+00:00
-- url     : https://prove2.me/theorems/3ec4da32-b1a2-40dc-9ff2-165ffd624aa4
-- title:
--   Aether Catalog definitions — Geometry_RomanDomination_Variants
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.RomanDomination.Variants`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/RomanDomination/Variants.lean by skeleton subtraction
import Mathlib
/-
# Roman-type domination parameters and the inequality chain

This file develops, from scratch, the family of *Roman-type domination* parameters
studied in the literature on Roman domination and its variants:

* the **domination number** `gammaDom G`,
* the **Roman domination number** `gammaR G`,
* the **Italian (a.k.a. Roman-{2}) domination number** `gammaI G`,
* the **double Roman domination number** `gammaDR G`,
* the **perfect Roman domination number** `gammaPR G`,
* the **unique response Roman domination number** `gammaUR G`.

All of them are defined as an infimum of the weight `∑ v, f v` over a class of
functions `f : V → ℕ` satisfying a local protection condition, and all of them are
well defined (the defining set of weights is non-empty) for every finite graph.

The main results are the classical comparison inequalities relating these six
parameters, together with the general upper bound `γ_R(G) ≤ n` and the exact value
`γ_R(G) = n` for the edgeless graph.
-/


namespace RomanDomination

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The weight of a labelling `f : V → ℕ` is the sum of its values. -/
def weight (f : V → ℕ) : ℕ := ∑ v, f v

section Defs

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- `S` dominates `G` if every vertex lies in `S` or has a neighbour in `S`. -/
def IsDominating (S : Finset V) : Prop := ∀ v, v ∈ S ∨ ∃ u ∈ S, G.Adj v u

/-- A *Roman dominating function*: values in `{0,1,2}` such that every vertex
labelled `0` has a neighbour labelled `2`. -/
def IsRDF (f : V → ℕ) : Prop :=
  (∀ v, f v ≤ 2) ∧ ∀ v, f v = 0 → ∃ u, G.Adj v u ∧ f u = 2

/-- An *Italian* (Roman-`{2}`) *dominating function*: values in `{0,1,2}` such that
the labels in the neighbourhood of any `0`-vertex sum to at least `2`. -/
def IsIDF (f : V → ℕ) : Prop :=
  (∀ v, f v ≤ 2) ∧ ∀ v, f v = 0 → 2 ≤ ∑ u ∈ G.neighborFinset v, f u

/-- A *double Roman dominating function*: values in `{0,1,2,3}` such that every
`0`-vertex has either a neighbour labelled `3` or two neighbours labelled at least `2`,
and every `1`-vertex has a neighbour labelled at least `2`. -/
def IsDRDF (f : V → ℕ) : Prop :=
  (∀ v, f v ≤ 3) ∧
  (∀ v, f v = 0 → (∃ u, G.Adj v u ∧ f u = 3) ∨
      ∃ u w, u ≠ w ∧ G.Adj v u ∧ G.Adj v w ∧ 2 ≤ f u ∧ 2 ≤ f w) ∧
  (∀ v, f v = 1 → ∃ u, G.Adj v u ∧ 2 ≤ f u)

/-- A *perfect Roman dominating function*: values in `{0,1,2}` and every `0`-vertex
has **exactly one** neighbour labelled `2`. -/
def IsPRDF (f : V → ℕ) : Prop :=
  (∀ v, f v ≤ 2) ∧ ∀ v, f v = 0 → ∃! u, G.Adj v u ∧ f u = 2

/-- A *unique response Roman dominating function*: every `0`-vertex has exactly one
neighbour labelled `2`, and no vertex with a positive label has a neighbour labelled `2`. -/
def IsURRDF (f : V → ℕ) : Prop :=
  (∀ v, f v ≤ 2) ∧ (∀ v, f v = 0 → ∃! u, G.Adj v u ∧ f u = 2) ∧
  (∀ v, 1 ≤ f v → ∀ u, G.Adj v u → f u ≠ 2)

/-- The domination number `γ(G)`. -/
noncomputable def gammaDom : ℕ := sInf {k | ∃ S : Finset V, IsDominating G S ∧ S.card = k}

/-- The Roman domination number `γ_R(G)`. -/
noncomputable def gammaR : ℕ := sInf {w | ∃ f, IsRDF G f ∧ weight f = w}

/-- The Italian (Roman-`{2}`) domination number `γ_I(G)`. -/
noncomputable def gammaI : ℕ := sInf {w | ∃ f, IsIDF G f ∧ weight f = w}

/-- The double Roman domination number `γ_dR(G)`. -/
noncomputable def gammaDR : ℕ := sInf {w | ∃ f, IsDRDF G f ∧ weight f = w}

/-- The perfect Roman domination number `γ_p(G)`. -/
noncomputable def gammaPR : ℕ := sInf {w | ∃ f, IsPRDF G f ∧ weight f = w}

/-- The unique response Roman domination number `u(G)`. -/
noncomputable def gammaUR : ℕ := sInf {w | ∃ f, IsURRDF G f ∧ weight f = w}

end Defs

section Basic

variable (G : SimpleGraph V) [DecidableRel G.Adj]









/-! ### Membership and minimality plumbing -/















end Basic

/-! ### Elementary weight computations -/

section WeightLemmas

variable (f : V → ℕ) (S : Finset V)







end WeightLemmas

/-! ### Transfer constructions between the variants -/

section Constructions

variable (G : SimpleGraph V) [DecidableRel G.Adj]








end Constructions

/-! ### The chain of inequalities -/

section Chain

variable (G : SimpleGraph V) [DecidableRel G.Adj]













end Chain

section Bounds

variable (G : SimpleGraph V) [DecidableRel G.Adj]





end Bounds

end RomanDomination


