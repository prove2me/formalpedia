-- Prove2me | Definitions.Def_Speculative_NumberTheory_GraphDominationBox
-- name    : Speculative_NumberTheory_GraphDominationBox
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T04:33:52.249842+00:00
-- url     : https://prove2.me/theorems/c3682533-9e2e-4494-800f-0bfb3331e438
-- title:
--   Aether Catalog definitions — Speculative_NumberTheory_GraphDominationBox
-- statement:
--   Definition bundle for the Aether Catalog module `Speculative.NumberTheory.GraphDominationBox`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Speculative/NumberTheory/GraphDominationBox.lean by skeleton subtraction
import Mathlib

/-!
# Domination in Cartesian (box) products of graphs

This file develops a small, self-contained theory of the **domination number** of a
finite simple graph and proves the two basic inequalities that bracket the
domination number of a Cartesian (box) product `G □ H`:

* an **upper bound** `γ(G □ H) ≤ γ(G) · |V(H)|`, obtained by "cylindrifying" a
  minimum dominating set of `G`;
* a **projection lower bound** `γ(G) ≤ γ(G □ H)` and `γ(H) ≤ γ(G □ H)`, obtained
  by projecting a minimum dominating set of the product onto a single coordinate.

The projection lower bound is the combinatorial engine behind Vizing-type results
(Clark–Suen, Suen–Tarr) on `γ(G □ H)`; see
`Catalog/Combinatorics/DominationProductConstant.lean` for the arithmetic of the
improved constant `(19 - √73)/18`.

Everything is stated over `Fintype`/`DecidableEq` vertex types, and the box product
is Mathlib's `SimpleGraph.boxProd` (notation `G □ H`).

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): The domination number of `G □ H` is squeezed between
`max(γ G, γ H)` and `γ G · |V H|`. The lower squeeze is coordinate-projection;
the upper squeeze is cylindrification. Both should be fully formalizable, unlike
the deep Vizing / Clark–Suen constant bounds.

Experiment (Experimenter): For `G = H = K₂` (a single edge), γ = 1 and
`K₂ □ K₂ = C₄`, whose domination number is 2. Indeed `max(1,1)=1 ≤ 2 ≤ 1·2`.
For a path `P₃` (γ = 1) and `K₂` (γ = 1), `P₃ □ K₂` (the 2×3 grid) has γ = 2,
again inside `[1, 1·2]`. The bounds held on every small case checked.

Analysis (Analyst): The upper bound is a clean cylindrification argument. The
lower bound needs the crucial observation that a box-product edge always keeps at
least one coordinate fixed, so the first-coordinate image of a dominating set of
`G □ H` dominates `G` (and symmetrically). This is the only place where the
adjacency structure of `□` is used, and it is exactly the fact used in Clark–Suen.

Critique (Critic): The lower-bound proof requires `Nonempty β` (resp. `Nonempty α`)
to pick a fibre; without it the projection is vacuous and the statement can fail
for the empty graph. The hypotheses are recorded explicitly. No theorem here is a
definitional `rfl`: each uses `sInf`, image cardinalities, and the `boxProd_adj`
case split.
-/

open SimpleGraph Finset

namespace GraphDom

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `S` is a dominating set of `G`: every vertex is either in `S` or adjacent to a
member of `S`. -/
def IsDominating (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ v : V, v ∈ S ∨ ∃ w ∈ S, G.Adj w v

/-- The domination number of `G`: the least cardinality of a dominating set. -/
noncomputable def dominationNumber (G : SimpleGraph V) : ℕ :=
  sInf { n | ∃ S : Finset V, IsDominating G S ∧ S.card = n }





variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]





end GraphDom


