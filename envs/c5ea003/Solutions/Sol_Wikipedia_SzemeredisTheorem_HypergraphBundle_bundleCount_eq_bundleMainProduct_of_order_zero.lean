-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.HypergraphBundle.bundleCount_eq_bundleMainProduct_of_order_zero
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:19:56.299749+00:00
-- url     : https://prove2.me/submissions/95d30430-bd78-459c-8f4d-caa86fafc23c

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







/-- Every edge cardinality is bounded by the order of the bundle. -/
theorem edge_card_le_order
    (B : HypergraphBundle J K H)
    {g : Finset K} (hg : g ∈ B.edges) :
    g.card ≤ B.order := by
  exact Finset.le_sup hg











/-! ## Local tuples and pulled-back base weights -/













@[simp]
theorem pullbackBaseEdgeWeight_of_mem
    (B : HypergraphBundle J K H)
    (A : BaseEdgeWeight J G)
    {g : Finset K} (hg : g ∈ B.edges)
    (y : {v : K // v ∈ g} → G) :
    B.pullbackBaseEdgeWeight A g y =
      A (g.image B.projection)
        (B.projectedEdgeTuple hg y) := by
  classical
  simp [pullbackBaseEdgeWeight, hg]



/-! ## Bundle products and normalized counts -/





























/-! ## Freezing the outside variables -/

























/-! ## Localized Cauchy--Schwarz and the doubled remainder -/

















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
/-! ## Elementary main-product and induction helpers -/

open Wikipedia.SzemeredisTheorem.HypergraphBundle in
/-- Neutral empty-edge weights make every order-zero bundle count exact. -/
theorem solution
    [Fintype K] [Fintype G] [Nonempty G]
    (B : HypergraphBundle J K H)
    (A : BaseEdgeWeight J G)
    (p : Finset J → ℝ)
    (hAempty :
      ∀ y :
        {j : J // j ∈ (∅ : Finset J)} → G,
        A ∅ y = 1)
    (hpempty : p ∅ = 1)
    (horder : B.order = 0) :
    B.bundleCount (B.pullbackBaseEdgeWeight A) =
      B.bundleMainProduct p := by
  have hedgeEmpty :
      ∀ g ∈ B.edges, g = ∅ := by
    intro g hg
    apply Finset.card_eq_zero.mp
    exact Nat.le_zero.mp
      (horder ▸ B.edge_card_le_order hg)
  have hproduct :
      ∀ x : K → G,
        B.bundleProduct
            (B.pullbackBaseEdgeWeight A) x = 1 := by
    intro x
    unfold bundleProduct
    apply Finset.prod_eq_one
    intro g hg
    have hge : g = ∅ :=
      hedgeEmpty g hg
    subst g
    rw [B.pullbackBaseEdgeWeight_of_mem A hg]
    exact hAempty _
  have hmain :
      B.bundleMainProduct p = 1 := by
    unfold bundleMainProduct
    apply Finset.prod_eq_one
    intro g hg
    rw [hedgeEmpty g hg]
    simp [hpempty]
  rw [hmain]
  unfold bundleCount
  calc
    mean
        (B.bundleProduct
          (B.pullbackBaseEdgeWeight A)) =
        mean (fun _x : K → G => 1) := by
      apply congrArg mean
      funext x
      exact hproduct x
    _ = 1 := mean_const 1
