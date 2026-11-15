-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.HypergraphBundle.duplicateOutside_closed
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:13:01.349198+00:00
-- url     : https://prove2.me/submissions/807f2109-a71c-4579-a3b4-be7510a112e6

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleDuplication
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Theorems.Thm_Wikipedia_SzemeredisTheorem_HypergraphBundle_doubledEdge_image_forget_of_subset

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section



/-!
# Hypergraph bundles and the counting-lemma decomposition

Tao's hypergraph counting lemma is proved after passing from one copy of
each vertex class to a *hypergraph bundle*.  A bundle has a finite set of
occurrence vertices, a finite family of occurrence edges, and a projection
to the base vertex classes which is injective on every occurrence edge.
The extra occurrence vertices record the copies created by repeated
Cauchy--Schwarz.

This file supplies the finite bundle object and the exact analytic
identities at one step of the double induction.  For a selected edge `g₀`,
the bundle count is split according to

```
edgeWeight = main + defect + uniform.
```

The uniform contribution is rewritten by freezing all variables outside
`g₀`.  The defect contribution is bounded by Cauchy--Schwarz; the second
factor is written exactly as an average with two independent copies of the
outside variables.  This is the doubled lower-rank bundle appearing in
Tao's proof.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators



namespace HypergraphBundle

variable {J K G : Type*}
  [DecidableEq J] [DecidableEq K]
  {H : Finset (Finset J)}











@[simp]
theorem eraseEdge_edges
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    (B.eraseEdge g₀).edges = B.edges.erase g₀ :=
  rfl







/-! ## Local tuples and pulled-back base weights -/

















/-! ## Bundle products and normalized counts -/





























/-! ## Freezing the outside variables -/

























/-! ## Localized Cauchy--Schwarz and the doubled remainder -/

















end HypergraphBundle

end Wikipedia.SzemeredisTheorem

end

section


/-!
# Duplicating the variables outside one bundle edge

The squared remainder in the bundle counting argument identifies the
variables on a selected edge `g₀` and takes two independent copies of every
variable outside `g₀`.  This file realizes that operation as a finite
hypergraph bundle.

An occurrence vertex in the doubled bundle is either a shared vertex of
`g₀`, or an outside vertex together with a Boolean copy label.  Every
remaining occurrence edge is lifted once into each copy.  The lift is
injective, preserves edge cardinality and projected base edges, and
therefore produces another valid bundle over the same base hypergraph.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

namespace HypergraphBundle

variable {J K G : Type*}
  [DecidableEq J] [DecidableEq K]
  {H : Finset (Finset J)}





























































@[simp]
theorem duplicateOutside_edges
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    (B.duplicateOutside g₀).edges =
      B.doubledEdges g₀ :=
  rfl































end HypergraphBundle

end Wikipedia.SzemeredisTheorem

end
/-!
# Duplicating the variables outside one bundle edge

The squared remainder in the bundle counting argument identifies the
variables on a selected edge `g₀` and takes two independent copies of every
variable outside `g₀`.  This file realizes that operation as a finite
hypergraph bundle.

An occurrence vertex in the doubled bundle is either a shared vertex of
`g₀`, or an outside vertex together with a Boolean copy label.  Every
remaining occurrence edge is lifted once into each copy.  The lift is
injective, preserves edge cardinality and projected base edges, and
therefore produces another valid bundle over the same base hypergraph.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
open Wikipedia.SzemeredisTheorem.HypergraphBundle
variable {J K G : Type*}
  [DecidableEq J] [DecidableEq K]
  {H : Finset (Finset J)}

open Wikipedia.SzemeredisTheorem.HypergraphBundle in
/-- Downward closure is preserved whenever it is already available after
erasing the selected edge. -/
theorem solution
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (hclosed :
      (B.eraseEdge g₀).IsClosedUnderInclusion) :
    (B.duplicateOutside g₀).IsClosedUnderInclusion := by
  intro d hd f hfd
  obtain ⟨copy, g, hg, rfl⟩ :=
    (B.mem_doubledEdges_iff g₀ d).1 hd
  let h : Finset K :=
    f.image (doubledVertexForget g₀)
  have hhg : h ⊆ g := by
    intro v hv
    obtain ⟨w, hw, hwv⟩ := Finset.mem_image.mp hv
    obtain ⟨u, hu, huw⟩ :=
      Finset.mem_image.mp (hfd hw)
    rw [← hwv, ← huw]
    simpa using hu
  have hh : h ∈ B.edges.erase g₀ :=
    hclosed hg hhg
  have hlift :
      doubledEdge g₀ copy h = f :=
    doubledEdge_image_forget_of_subset
      g₀ copy hfd
  rw [← hlift]
  exact
    (B.mem_doubledEdges_iff g₀
      (doubledEdge g₀ copy h)).2
      ⟨copy, h, hh, rfl⟩
