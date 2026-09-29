-- Prove2me | Definitions.Def_Cryptography_UniversalPosets_Comparability
-- name    : Cryptography_UniversalPosets_Comparability
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:27:48.111565+00:00
-- url     : https://prove2.me/theorems/4b5cf480-301c-410d-9850-548d629540b7
-- title:
--   Aether Catalog definitions — Cryptography_UniversalPosets_Comparability
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.UniversalPosets.Comparability`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/UniversalPosets/Comparability.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Cryptography_UniversalPosets_Bounds

/-!
# Comparability graphs: a bridge from universal posets to universal graphs

The motivating paper transports poset problems to graph problems (and uses the
Szemerédi Regularity Lemma on the resulting graphs).  This file formalises the
transport.

* `comparabilityGraph r` is the comparability graph of an order relation `r`.
* `comparabilityGraph_bipRel` identifies the comparability graph of a height-`≤ 2`
  ("bipartite") poset with the corresponding bipartite graph -- an exact
  equality of graphs, not merely an embedding.
* `IsBipartiteUniversalGraph` is the graph analogue of `IsBipartiteUniversal`
  and satisfies the same counting bound `2 ^ (k*l) ≤ N ^ (k+l)`.
* `isBipartiteUniversalGraph_of_isBipartiteUniversal` says the comparability
  graph of a universal *poset* host is a universal *graph* host; hence the
  poset lower bound of `Bounds.lean` is *re-derived* from the graph one
  (`two_pow_mul_le_card_pow_via_graphs`), a genuinely different proof route.
* `comparability_regularity` instantiates Mathlib's Szemerédi Regularity Lemma
  for comparability graphs of finite posets, which is the form in which the
  regularity method enters the study of universal posets.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer).  (1) Comparability is a *functor* on induced
embeddings; (2) the height-2 family is mapped onto the whole family of
bipartite graphs, bijectively on relations; (3) therefore the poset counting
bound and the graph counting bound are the same theorem viewed twice; (4)
regularity applies verbatim to comparability graphs.

Experiment (Experimenter).  (1)-(4) proved.  The subtle point in (1) is that a
merely order-preserving map does *not* induce an induced subgraph: reflection of
the order is needed, and injectivity is needed to keep non-adjacent pairs
distinct; both are supplied by `injective_of_universal_witness`.

Analysis (Analyst).  The graph route loses nothing for the bipartite class,
which explains why regularity-based graph technology (as in the paper) is the
right tool: no information is destroyed when passing from a height-2 poset to
its comparability graph.  For general posets the functor *does* lose
information (the comparability graph forgets orientation), which is exactly the
reason the paper must re-orient after applying graph tools.

Critique (Critic).  `comparability_regularity` is an instantiation of Mathlib's
regularity lemma, and is presented as such; the mathematical content of this
file is in the functor and the counting bound, both proved from scratch.
-/

open Finset Fintype

namespace UniversalPosets

variable {k l : ℕ}

/-! ## The comparability graph -/

/-- The comparability graph of a relation: distinct points joined when comparable. -/
def comparabilityGraph {α : Type*} (r : α → α → Prop) : SimpleGraph α where
  Adj x y := x ≠ y ∧ (r x y ∨ r y x)
  symm := by
    rintro x y ⟨h1, h2⟩
    exact ⟨h1.symm, h2.symm⟩
  loopless := ⟨fun _ h => h.1 rfl⟩


instance comparabilityGraph_decidableAdj {α : Type*} [DecidableEq α] (r : α → α → Prop)
    [DecidableRel r] : DecidableRel (comparabilityGraph r).Adj :=
  fun x y => inferInstanceAs (Decidable (x ≠ y ∧ (r x y ∨ r y x)))

/-- The bipartite graph of a bipartite relation. -/
def bipGraph (R : Fin k → Fin l → Bool) : SimpleGraph (Fin k ⊕ Fin l) where
  Adj x y :=
    match x, y with
    | Sum.inl a, Sum.inr b => R a b
    | Sum.inr b, Sum.inl a => R a b
    | _, _ => False
  symm := by rintro (a | a) (b | b) h <;> simp_all
  loopless := ⟨by rintro (a | a) h <;> simp at h⟩

instance bipGraph_decidableAdj (R : Fin k → Fin l → Bool) : DecidableRel (bipGraph R).Adj :=
  fun x y =>
    match x, y with
    | Sum.inl _, Sum.inl _ => inferInstanceAs (Decidable False)
    | Sum.inl a, Sum.inr b => inferInstanceAs (Decidable (R a b = true))
    | Sum.inr b, Sum.inl a => inferInstanceAs (Decidable (R a b = true))
    | Sum.inr _, Sum.inr _ => inferInstanceAs (Decidable False)


/-! ## Universal graphs for the bipartite class -/

/--
`IsBipartiteUniversalGraph H k l` : the graph `H` contains every `(k,l)`-bipartite
graph as an induced subgraph.
-/
def IsBipartiteUniversalGraph {V : Type*} (H : SimpleGraph V) (k l : ℕ) : Prop :=
  ∀ R : Fin k → Fin l → Bool, ∃ f : (Fin k ⊕ Fin l) → V,
    ∀ x y, H.Adj (f x) (f y) ↔ (bipGraph R).Adj x y


/-! ## The comparability functor -/



/-! ## Regularity for comparability graphs -/



end UniversalPosets


