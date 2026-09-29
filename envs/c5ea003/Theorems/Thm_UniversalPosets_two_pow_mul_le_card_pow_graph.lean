-- Prove2me | Theorems.Thm_UniversalPosets_two_pow_mul_le_card_pow_graph
-- name    : UniversalPosets.two_pow_mul_le_card_pow_graph
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T03:08:05.07575+00:00
-- url     : https://prove2.me/theorems/8c400d03-ccc0-488e-bf22-86202a51602b
-- title:
--   Counting lower bound for induced-universal graphs.
-- statement:
--   **Counting lower bound for induced-universal graphs.**  A host graph on `N`
--   vertices containing all `(k,l)`-bipartite graphs as induced subgraphs satisfies
--   `2 ^ (k*l) ≤ N ^ (k+l)`.
--
--   ```lean
--   theorem UniversalPosets.two_pow_mul_le_card_pow_graph{V : Type*} [Fintype V] {H : SimpleGraph V}
--       (h : IsBipartiteUniversalGraph H k l) :
--       2 ^ (k * l) ≤ (Fintype.card V) ^ (k + l) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/UniversalPosets/Comparability.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/UniversalPosets/Comparability.lean#L109

-- Thm stub generated from Cryptography/UniversalPosets/Comparability.lean
import Mathlib
import Definitions.Def_Cryptography_UniversalPosets_Bounds
import Definitions.Def_Cryptography_UniversalPosets_Comparability

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

open UniversalPosets

variable {k l : ℕ}

/-! ## The comparability graph -/







/-! ## Universal graphs for the bipartite class -/

theorem UniversalPosets.two_pow_mul_le_card_pow_graph{V : Type*} [Fintype V] {H : SimpleGraph V}
    (h : IsBipartiteUniversalGraph H k l) :
    2 ^ (k * l) ≤ (Fintype.card V) ^ (k + l) := by sorry
