-- Prove2me | Definitions.Def_Logic_HamiltonCoverLinearArboricityBridge
-- name    : Logic_HamiltonCoverLinearArboricityBridge
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T13:54:27.412722+00:00
-- url     : https://prove2.me/theorems/c4718c7f-d5e4-4ca9-9b56-37a0cba6db82
-- title:
--   Aether Catalog definitions — Logic_HamiltonCoverLinearArboricityBridge
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.HamiltonCoverLinearArboricityBridge`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/HamiltonCoverLinearArboricityBridge.lean by skeleton subtraction
import Mathlib

/-!
# Hamilton covers, incidence codes, and punctured linear systems

This file isolates two deterministic mechanisms behind efficient Hamilton covers.
A family of two-regular spanning layers is simultaneously:

* a constant-column-weight incidence code, which forces the maximum-degree lower bound; and
* after deleting one distinguished edge per layer, a family of punctured layers covering every
  edge except a small transversal.  When the layers are Hamilton cycles, these punctured layers
  are Hamilton paths and hence linear forests.

The theorem is deliberately stated for an arbitrary finite edge type and incidence relation.  It
therefore applies to simple graphs, multigraphs, and auxiliary graph systems without changing the
counting argument.
-/

namespace HamiltonCoverBridge

variable {V E I : Type*} [DecidableEq E]

/-- Number of edges in `F` incident with `v`. -/
def incidenceDegree (incident : E → V → Prop) [DecidableRel incident]
    (F : Finset E) (v : V) : ℕ :=
  (F.filter fun e => incident e v).card

/-- A layer is two-regular at every vertex (the local property of a Hamilton cycle). -/
def TwoRegular (incident : E → V → Prop) [DecidableRel incident]
    (C : Finset E) : Prop :=
  ∀ v, incidenceDegree incident C v = 2

/-- The layers cover the target edge set. -/
def Covers (target : Finset E) (layer : I → Finset E) : Prop :=
  ∀ e ∈ target, ∃ i, e ∈ layer i

/-- Delete one distinguished edge from every layer. -/
def puncture (layer : I → Finset E) (chosen : I → E) (i : I) : Finset E :=
  (layer i).erase (chosen i)

/-- The incidence code at a vertex: layer `i` contributes the incident edges in that layer. -/
def incidenceCode (incident : E → V → Prop) [DecidableRel incident]
    (layer : I → Finset E) (v : V) (i : I) : Finset E :=
  (layer i).filter fun e => incident e v

/-
A covered degree is bounded by the total Hamming weight of its incidence-code blocks.
-/

/-
**Coding-theoretic lower bound for Hamilton covers.**
Every block of the incidence code of a two-regular layer has weight two.  Consequently a cover
of `d` edges incident with a vertex requires at least `⌈d/2⌉` layers.
-/

/-
Puncturing one edge in every layer loses no target edge outside the chosen transversal.
-/

/-
**Connector theorem.** A two-regular edge cover gives at once
(1) the sharp degree/2 obstruction, viewed as a Hamming-weight bound, and
(2) a punctured cover outside a transversal of at most one edge per layer.

For Hamilton-cycle layers, the punctured objects are Hamilton paths, so conclusion (2) is exactly
the deterministic bridge from Hamilton covers to linear-forest covers used in linear arboricity.
-/

end HamiltonCoverBridge


