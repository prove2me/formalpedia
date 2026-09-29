-- Prove2me | Definitions.Def_Logic_TopoErrorMitigation_PersistentH0
-- name    : Logic_TopoErrorMitigation_PersistentH0
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T14:08:34.216115+00:00
-- url     : https://prove2.me/theorems/58fba10c-81b1-490a-8ebe-db91b236383c
-- title:
--   Aether Catalog definitions — Logic_TopoErrorMitigation_PersistentH0
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.TopoErrorMitigation.PersistentH0`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/TopoErrorMitigation/PersistentH0.lean by skeleton subtraction
import Mathlib

/-!
# Zeroth Persistent Betti Number is Monotone Along a Filtration

This file formalises the algebraic-topology half of the Phase-A bridge
`Logic ↔ Algebraic Topology`.  In persistent homology the data of a NISQ
experiment is organised as a *filtration*: as a proximity threshold `t`
increases, more pairs of measurement outcomes are linked, and connected
components (the zeroth homology `H₀`) can only **merge**, never split.  The
number of connected components is the *zeroth Betti number* `β₀`; its decay along
the filtration is exactly the birth/death structure of the `H₀` barcode.

We model a filtration step by two relations `r₁ ⊆ r₂` on a finite vertex type
`V` (think: "linked at threshold `t₁`" refines "linked at threshold `t₂`").  The
connected components are the classes of the equivalence closure
`Relation.EqvGen`.  We prove `β₀(r₂) ≤ β₀(r₁)`: persistence of `H₀`.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): The number of connected components of a proximity
  graph is monotone non-increasing as edges are added — components only merge.
Experiment (Experimenter): Modelled components as `Quot (Relation.EqvGen r)`.
  Built a well-defined map from the finer quotient to the coarser one via
  `Quot.lift` and `Relation.EqvGen.mono`, then showed it is surjective.
Analysis (Analyst): The decreasing-cardinality follows from
  `Fintype.card_le_of_surjective`; the surjection exists because the coarser
  `Quot.mk` is surjective and factors through our map.  Key structural insight:
  monotonicity of `EqvGen` in its base relation is the topological content
  ("adding edges cannot create components").
Critique (Critic): The `Fintype` instances on the quotients are genuine
  hypotheses (a quotient of a finite type need not be `DecidableEq`-computable),
  so they are taken as instance arguments rather than derived — keeping the
  statement honest.  Non-degeneracy is witnessed by `componentMap_merges`, an
  explicit instance over `Bool` where two distinct components are merged.
Synthesis (PI): `betti0_persistence` — `H₀` persistence — plus its corollary
  packaging for an explicit NISQ proximity filtration.
-/

namespace TopoErrorMitigation

open Relation

variable {V : Type*}

/-- The zeroth Betti number of a relation: the number of connected components,
i.e. classes of the equivalence closure of `r`. -/
noncomputable def betti0 (r : V → V → Prop) [Fintype (Quot (EqvGen r))] : ℕ :=
  Fintype.card (Quot (EqvGen r))

/-- The component map induced by a refinement `r₁ ⊆ r₂` of relations:
it sends the `r₁`-component of a point to its (coarser) `r₂`-component. -/
def componentMap (r₁ r₂ : V → V → Prop) (h : ∀ a b, r₁ a b → r₂ a b) :
    Quot (EqvGen r₁) → Quot (EqvGen r₂) :=
  Quot.lift (fun a => Quot.mk _ a)
    (fun _ _ hab => Quot.sound (EqvGen.mono h hab))




end TopoErrorMitigation


