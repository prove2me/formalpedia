-- Prove2me | Definitions.Def_Probability_HadwigerCriticalEquiv
-- name    : Probability_HadwigerCriticalEquiv
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T13:58:37.309126+00:00
-- url     : https://prove2.me/theorems/9a921394-aebd-4730-af13-596e4ab54948
-- title:
--   Aether Catalog definitions — Probability_HadwigerCriticalEquiv
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.HadwigerCriticalEquiv`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/HadwigerCriticalEquiv.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Probability_HadwigerCritical
import Definitions.Def_Probability_HadwigerK3
/-
  # Hadwiger's conjecture is equivalent to its vertex-critical fragment

  This file settles the vertex-critical form of Conjecture 4 of
  `FUTURE_DIRECTIONS.md`: Hadwiger's conjecture for a parameter `k` need only be
  checked on *vertex-critical* graphs, i.e. graphs that are not `k`-colourable
  but become `k`-colourable after the deletion of any single vertex.

      `HadwigerProperty k ↔ HadwigerCriticalProperty k`   (`hadwigerProperty_iff_critical`)

  The `←` direction is the substantial one: a minimal non-`k`-colourable vertex
  subset (`exists_critical_subset`, from `HadwigerCritical.lean`) induces a
  vertex-critical subgraph, and a `K_{k+1}` minor of an induced subgraph is a
  `K_{k+1}` minor of the ambient graph (`isMinor_of_isMinor_induce`).

  The bridge between the ambient-colouring predicate `ColorableOn` and
  colourability of the induced subgraph is `colorableOn_iff_induce`, valid as
  soon as one colour is available; the degenerate parameter `k = 0` is covered by
  the already-proved `hadwiger_zero`.

  -- !-- Lab Notes -- !--
  * No graph isomorphism is needed to see that deleting a vertex from an induced
    subgraph is again an induced subgraph: a colouring of `G.induce ↑(S.erase x)`
    can be *restricted* along the two coercions, which is what
    `colorable_induce_compl_of_colorableOn_erase` does.
  * The equivalence makes "minimal counterexample" arguments available inside the
    formal development: any counterexample to `HadwigerProperty k` yields a
    vertex-critical one.
-/

namespace Hadwiger

open SimpleGraph Finset

variable {V : Type*} {G : SimpleGraph V} {k : ℕ}



/-- **Hadwiger's conjecture restricted to vertex-critical graphs**: graphs that
are not `k`-colourable but in which the deletion of any single vertex restores
`k`-colourability. -/
def HadwigerCriticalProperty (k : ℕ) : Prop :=
  ∀ (V : Type) [Finite V] (G : SimpleGraph V), ¬ G.Colorable k →
    (∀ v : V, (G.induce ({v}ᶜ : Set V)).Colorable k) → CompleteMinor (k + 1) G


/-! ## The minimum-degree fragment -/

/-- **Hadwiger's conjecture restricted to graphs of minimum degree at least `k`.**
Unlike the hypothesis of `hadwigerProperty_of_minDegree_forces`, the graph is
here also assumed not to be `k`-colourable, which makes the restriction
*equivalent* to the full conjecture rather than strictly stronger. -/
def HadwigerMinDegreeProperty (k : ℕ) : Prop :=
  ∀ (V : Type) [Finite V] (G : SimpleGraph V), ¬ G.Colorable k →
    (∀ v : V, k ≤ Nat.card (G.neighborSet v)) → CompleteMinor (k + 1) G



end Hadwiger


