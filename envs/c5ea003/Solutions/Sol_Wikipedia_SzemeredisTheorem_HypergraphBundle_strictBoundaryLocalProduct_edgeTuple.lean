-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.HypergraphBundle.strictBoundaryLocalProduct_edgeTuple
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:18:05.885211+00:00
-- url     : https://prove2.me/submissions/ab045af7-2bfe-4edf-ab6b-0983d8f7b58c

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleDuplication
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleFiltration
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleGeneralizedCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleIndicatorDuplication
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

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















/-! ## The lower-order and strict-boundary filtrations -/

















@[simp]
theorem strictBoundary_edges
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    (B.strictBoundary g₀).edges =
      B.edges.filter fun g => g ⊂ g₀ :=
  rfl











/-! ## Main-density products -/













/-! ## The main product under duplication -/













end HypergraphBundle

end Wikipedia.SzemeredisTheorem

end

section



/-!
# Generalized counting for closed hypergraph bundles

This file packages the part of Tao's generalized counting argument which
is specific to hypergraph bundles.

There are two points which are easy to lose in a scalar recurrence.

* The defect at a selected maximal edge is localized to the product of
  the strict-boundary indicators.  Since those indicators already occur
  among the remaining bundle factors, idempotence lets us insert that
  boundary product without changing the contribution.
* After Cauchy--Schwarz, all remaining maximal-rank indicator factors may
  be discarded.  The resulting moment is the count of the duplicated
  lower-order bundle.  Its main-density product contains one copy of the
  strict boundary and two copies of every other lower-order edge.

The last section records a flexible numerical envelope for the ensuing
double induction.  It deliberately separates the same-rank density floor
`α` from the all-rank density floor `μ`: the defect term only loses powers
of `α`, while the common frozen-uniformity error may lose powers of `μ`.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

namespace HypergraphBundle

variable {J K G : Type*}
  [DecidableEq J] [DecidableEq K]
  {H : Finset (Finset J)}

/-! ## Local strict-boundary products -/



omit [DecidableEq K] in
@[simp]
theorem restrictEdgeTuple_edgeTuple
    {f g : Finset K} (hfg : f ⊆ g)
    (x : K → G) :
    restrictEdgeTuple hfg (edgeTuple g x) =
      edgeTuple f x := by
  rfl

















/-! ## Main-product cancellation at a selected edge -/























/-! ## Discarding the other maximal-rank factors -/











end HypergraphBundle

/-! ## Numerical envelope for the double induction -/









end Wikipedia.SzemeredisTheorem

end
/-!
# Generalized counting for closed hypergraph bundles

This file packages the part of Tao's generalized counting argument which
is specific to hypergraph bundles.

There are two points which are easy to lose in a scalar recurrence.

* The defect at a selected maximal edge is localized to the product of
  the strict-boundary indicators.  Since those indicators already occur
  among the remaining bundle factors, idempotence lets us insert that
  boundary product without changing the contribution.
* After Cauchy--Schwarz, all remaining maximal-rank indicator factors may
  be discarded.  The resulting moment is the count of the duplicated
  lower-order bundle.  Its main-density product contains one copy of the
  strict boundary and two copies of every other lower-order edge.

The last section records a flexible numerical envelope for the ensuing
double induction.  It deliberately separates the same-rank density floor
`α` from the all-rank density floor `μ`: the defect term only loses powers
of `α`, while the common frozen-uniformity error may lose powers of `μ`.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
open Wikipedia.SzemeredisTheorem.HypergraphBundle
variable {J K G : Type*}
  [DecidableEq J] [DecidableEq K]
  {H : Finset (Finset J)}
/-! ## Local strict-boundary products -/

open Wikipedia.SzemeredisTheorem.HypergraphBundle in
/-- The local strict-boundary product is exactly the ordinary bundle
product of the strict-boundary subbundle. -/
theorem solution
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    (x : K → G) :
    B.strictBoundaryLocalProduct g₀ A
        (edgeTuple g₀ x) =
      (B.strictBoundary g₀).bundleProduct A x := by
  classical
  unfold strictBoundaryLocalProduct
  calc
    (∏ g :
        {g : Finset K //
          g ∈ (B.strictBoundary g₀).edges},
      A g.1
        (restrictEdgeTuple
          (((B.mem_strictBoundary_edges g₀ g.1).1
            g.2).2.1)
          (edgeTuple g₀ x))) =
        ∏ g :
          {g : Finset K //
            g ∈ (B.strictBoundary g₀).edges},
          A g.1 (edgeTuple g.1 x) := by
      apply Finset.prod_congr rfl
      intro g _hg
      apply congrArg (A g.1)
      exact restrictEdgeTuple_edgeTuple _ x
    _ =
        ∏ g ∈ (B.strictBoundary g₀).edges,
          A g (edgeTuple g x) :=
      Finset.prod_coe_sort
        (B.strictBoundary g₀).edges
        (fun g => A g (edgeTuple g x))
    _ = (B.strictBoundary g₀).bundleProduct A x := by
      rfl
