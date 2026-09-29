-- Prove2me | Definitions.Def_Shared_RamseyTheory_CliqueComplexChain
-- name    : Shared_RamseyTheory_CliqueComplexChain
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T15:13:04.05461+00:00
-- url     : https://prove2.me/theorems/e8ff5935-028b-441c-8c16-8b2397c6b3b9
-- title:
--   Aether Catalog definitions — Shared_RamseyTheory_CliqueComplexChain
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.RamseyTheory.CliqueComplexChain`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/RamseyTheory/CliqueComplexChain.lean by skeleton subtraction
import Mathlib
/-
# The Simplicial Chain Complex of a Clique Complex over ℤ

The clique complex `Δ(G)` of a simple graph `G` is the abstract simplicial complex
whose `k`-faces are the `(k+1)`-cliques of `G`.  Choosing a linear order on the
vertex set turns the set of finite cliques into an *ordered* simplicial complex,
and the standard alternating-sum boundary operator

  ∂(s) = Σ_{x ∈ s} (-1)^{rank of x in s} · (s \ {x})

makes the free ℤ-modules on faces into a chain complex.

This file develops that chain complex purely combinatorially on `Finset V →₀ ℤ`
(the free ℤ-module on all finite subsets, of which the clique complex is a
downward-closed sub-object) and proves the defining identity `∂ ∘ ∂ = 0`.
We then connect it back to graphs: cliques are downward closed, and the boundary
of a clique-face is supported on clique-faces, so the construction restricts to a
genuine chain complex of `Δ(G)`.

The novelty here is a fully self-contained, order-theoretic proof of `∂² = 0`
via a sign-reversing involution on ordered pairs of vertices, packaged so that it
applies verbatim to the clique complex of an arbitrary simple graph.
-/

open Finset SimpleGraph

namespace CliqueComplexChain

variable {V : Type*} [LinearOrder V]

/-- The orientation sign of vertex `x` inside the ordered simplex `s`: it is
`(-1)` raised to the number of vertices of `s` strictly below `x`, i.e. the rank
(position) of `x` in the increasing enumeration of `s`. -/
def sgn (x : V) (s : Finset V) : ℤ := (-1) ^ (s.filter (· < x)).card

/-- The boundary of a single oriented simplex `s`, as a ℤ-linear combination of
its codimension-1 faces. -/
noncomputable def bdSingle (s : Finset V) : Finset V →₀ ℤ :=
  ∑ x ∈ s, Finsupp.single (s.erase x) (sgn x s)

/-- The boundary operator on the free ℤ-module of chains, extended linearly. -/
noncomputable def bd : (Finset V →₀ ℤ) →ₗ[ℤ] (Finset V →₀ ℤ) :=
  Finsupp.linearCombination ℤ bdSingle

-- !-- Evaluating the linear boundary on a basis chain just scales `bdSingle`. -- !--

/-
!-- If `x ∉ s` is not below `y`, erasing `x` does not change the rank of `y`,
so the sign is unchanged.  Uses `Finset.filter_erase`. -- !--
-/

/-
!-- If `x ∈ s` lies below `y`, erasing `x` drops the rank of `y` by one, so the
sign flips.  Uses `Finset.filter_erase` and `(-1)^(n+1) = -(-1)^n`. -- !--
-/

/-
!-- Core sign-cancellation: the two ways of removing an unordered pair `{x,y}`
from `s` carry opposite signs.  Case split on the trichotomy of `x` and `y`,
using `sgn_erase_lt` / `sgn_erase_not_lt`. -- !--
-/

/-
!-- The boundary of a boundary of one simplex vanishes.  Expand into a double
sum over ordered pairs `(x,y)`, reindex over `s.sigma (fun x => s.erase x)`,
and kill it with `Finset.sum_involution` using the swap `(x,y) ↦ (y,x)`:
paired terms hit the same face `(s.erase x).erase y = (s.erase y).erase x`
(`Finset.erase_right_comm`) with opposite signs by `sgn_swap`. -- !--
-/

/-
!-- `∂² = 0` on every chain, by `Finsupp.induction` reducing to `bd_bdSingle`. -- !--
-/

-- !-- The chain-complex identity `∂ ∘ ∂ = 0` as linear maps. -- !--

/-! ## Connection to the clique complex of a graph -/

/-- A finite set of vertices is a face of the clique complex of `G` iff it is a
clique. -/
def IsFace (G : SimpleGraph V) (s : Finset V) : Prop := G.IsClique (s : Set V)

-- !-- Faces are downward closed: a subset of a clique is a clique
-- (`SimpleGraph.IsClique.subset`). -- !--

-- !-- The empty face is always present. -- !--

-- !-- Every vertex is a `0`-face. -- !--

/-
!-- The boundary of a clique-face is supported on clique-faces, so `∂` really
maps clique-chains to clique-chains.  Each support element is some `s.erase x`,
a subset of `s`, hence a face by `isFace_downward_closed`. -- !--
-/

end CliqueComplexChain


