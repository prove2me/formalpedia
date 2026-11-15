-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.HypergraphBundle.bundleCount_decompose_edge
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T09:59:34.930082+00:00
-- url     : https://prove2.me/submissions/77642430-b8b7-4457-ac71-27d44e468487

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleCounting
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











@[simp]
theorem eraseEdge_edges
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    (B.eraseEdge g₀).edges = B.edges.erase g₀ :=
  rfl







/-! ## Local tuples and pulled-back base weights -/

















/-! ## Bundle products and normalized counts -/























/-- Factoring a selected edge out of the bundle product. -/
theorem bundleCount_eq_edgeContribution
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges) :
    B.bundleCount A =
      B.edgeContribution g₀ (A g₀) A := by
  unfold bundleCount edgeContribution edgeRemainder
  apply congrArg mean
  funext x
  exact
    (Finset.mul_prod_erase B.edges
      (fun g => A g (edgeTuple g x)) hg₀).symm





/-! ## Freezing the outside variables -/

























/-! ## Localized Cauchy--Schwarz and the doubled remainder -/

















end HypergraphBundle

end Wikipedia.SzemeredisTheorem

end
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
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
open Wikipedia.SzemeredisTheorem.HypergraphBundle
variable {J K G : Type*}
  [DecidableEq J] [DecidableEq K]
  {H : Finset (Finset J)}
/-! ## Local tuples and pulled-back base weights -/
/-! ## Bundle products and normalized counts -/

open Wikipedia.SzemeredisTheorem.HypergraphBundle in
/-- Exact main/defect/uniform decomposition at one selected edge. -/
theorem solution
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges)
    (p : ℝ)
    (b c : ({v : K // v ∈ g₀} → G) → ℝ)
    (hdecomp : ∀ y, A g₀ y = p + b y + c y) :
    B.bundleCount A =
      p * (B.eraseEdge g₀).bundleCount A +
        B.edgeContribution g₀ b A +
        B.edgeContribution g₀ c A := by
  rw [B.bundleCount_eq_edgeContribution A hg₀]
  unfold edgeContribution bundleCount
  calc
    mean (fun x : K → G =>
        A g₀ (edgeTuple g₀ x) *
          B.edgeRemainder g₀ A x) =
        mean (fun x : K → G =>
          p * B.edgeRemainder g₀ A x +
            b (edgeTuple g₀ x) *
              B.edgeRemainder g₀ A x +
            c (edgeTuple g₀ x) *
              B.edgeRemainder g₀ A x) := by
      apply congrArg mean
      funext x
      rw [hdecomp]
      ring
    _ =
        mean (fun x : K → G =>
          p * B.edgeRemainder g₀ A x) +
          mean (fun x : K → G =>
            b (edgeTuple g₀ x) *
              B.edgeRemainder g₀ A x) +
          mean (fun x : K → G =>
            c (edgeTuple g₀ x) *
              B.edgeRemainder g₀ A x) := by
      rw [mean_add, mean_add]
    _ =
        p * (B.eraseEdge g₀).bundleCount A +
          B.edgeContribution g₀ b A +
          B.edgeContribution g₀ c A := by
      rw [mean_smul]
      rfl
