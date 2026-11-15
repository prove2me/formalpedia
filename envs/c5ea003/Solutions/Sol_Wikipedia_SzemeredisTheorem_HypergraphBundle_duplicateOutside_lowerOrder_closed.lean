-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.HypergraphBundle.duplicateOutside_lowerOrder_closed
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:21:01.369804+00:00
-- url     : https://prove2.me/submissions/86a68c56-bd7c-42c2-b414-2e23f9fdfb43

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleDuplication
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleFiltration
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleGeneralizedCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleIndicatorDuplication
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleRelativeCounting
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Theorems.Thm_Wikipedia_SzemeredisTheorem_HypergraphBundle_duplicateOutside_closed

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

section


/-!
# Filtrations of hypergraph bundles

The generalized counting argument repeatedly discards all edges of the
current maximal rank and then duplicates the remaining bundle around one
selected maximal edge.  This file packages the elementary structural
operations used in that step.

Besides arbitrary edge filtering, we single out the lower-order part of a
bundle and the strict boundary below a fixed edge.  The final product
identity records the only collisions caused by duplication: the two
labelled copies of a strict boundary edge coincide, whereas every other
lower-order edge contributes two distinct copies.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

namespace HypergraphBundle

variable {J K : Type*}
  [DecidableEq J] [DecidableEq K]
  {H : Finset (Finset J)}

/-! ## Edge-filtered subbundles -/













/-- A hereditary edge predicate preserves downward closure. -/
theorem filterEdges_closed
    (B : HypergraphBundle J K H)
    (P : Finset K → Prop) [DecidablePred P]
    (hclosed : B.IsClosedUnderInclusion)
    (hP : ∀ ⦃g⦄, P g →
      ∀ ⦃f⦄, f ⊆ g → P f) :
    (B.filterEdges P).IsClosedUnderInclusion := by
  intro g hg f hfg
  have hg' := (B.mem_filterEdges_edges P g).1 hg
  exact (B.mem_filterEdges_edges P f).2
    ⟨hclosed hg'.1 hfg, hP hg'.2 hfg⟩

/-! ## The lower-order and strict-boundary filtrations -/



@[simp]
theorem lowerOrder_edges
    (B : HypergraphBundle J K H) (d : ℕ) :
    (B.lowerOrder d).edges =
      B.edges.filter fun g => g.card < d :=
  rfl

@[simp]
theorem mem_lowerOrder_edges
    (B : HypergraphBundle J K H)
    (d : ℕ) (g : Finset K) :
    g ∈ (B.lowerOrder d).edges ↔
      g ∈ B.edges ∧ g.card < d := by
  simp [lowerOrder]







theorem lowerOrder_closed
    (B : HypergraphBundle J K H)
    (hclosed : B.IsClosedUnderInclusion)
    (d : ℕ) :
    (B.lowerOrder d).IsClosedUnderInclusion := by
  apply B.filterEdges_closed _ hclosed
  intro g hg f hfg
  exact (Finset.card_le_card hfg).trans_lt hg















/-! ## Main-density products -/













/-! ## The main product under duplication -/













end HypergraphBundle

end Wikipedia.SzemeredisTheorem

end
/-!
# Relative generalized counting for closed hypergraph bundles

This file performs the double induction in Tao's generalized counting
lemma.  Its sole analytic input is `HasTaoBundleCountingStep`: at one
maximal occurrence edge, the count differs from the main density times
the erased count by the square root of two lower-order counts plus the
common frozen-uniformity error.

The induction first decreases bundle order and then, at fixed order,
decreases the number of occurrence edges.  The exact main-product
identities from `HypergraphBundleGeneralizedCounting` cancel every
lower-order density from the relative defect error.  Consequently the
defect term pays only the selected-rank floor `α`, while the absolute
uniform term pays the all-rank floor `μ`.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
open Wikipedia.SzemeredisTheorem.HypergraphBundle
variable {J K G : Type*}
  [DecidableEq J] [DecidableEq K]
  {H : Finset (Finset J)}
/-! ## Canonical pullbacks on subbundles -/
/-! ## Structural bounds for the two outer-induction bundles -/

open Wikipedia.SzemeredisTheorem.HypergraphBundle in
/-- The duplicated lower-order bundle remains downward closed. -/
theorem solution
    (B : HypergraphBundle J K H)
    (hclosed : B.IsClosedUnderInclusion)
    (g₀ : Finset K) :
    ((B.lowerOrder g₀.card).duplicateOutside g₀).IsClosedUnderInclusion := by
  apply (B.lowerOrder g₀.card).duplicateOutside_closed
    g₀
  intro g hg f hfg
  have hgLower :
      g ∈ (B.lowerOrder g₀.card).edges :=
    Finset.mem_of_mem_erase hg
  have hfLower :
      f ∈ (B.lowerOrder g₀.card).edges :=
    B.lowerOrder_closed hclosed g₀.card
      hgLower hfg
  apply Finset.mem_erase.mpr
  refine ⟨?_, hfLower⟩
  intro hfg₀
  subst f
  have hgcard :
      g.card < g₀.card :=
    ((B.mem_lowerOrder_edges g₀.card g).1
      hgLower).2
  have hcardle : g₀.card ≤ g.card :=
    Finset.card_le_card hfg
  exact (Nat.not_le_of_gt hgcard) hcardle
