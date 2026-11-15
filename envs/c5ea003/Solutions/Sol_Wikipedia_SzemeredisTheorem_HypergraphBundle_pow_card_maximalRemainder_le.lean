-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.HypergraphBundle.pow_card_maximalRemainder_le
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:16:25.318782+00:00
-- url     : https://prove2.me/submissions/9c67af68-4094-4883-858f-bd0fcaf1aa03

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





















/-! ## Main-product cancellation at a selected edge -/





/-- Projection preserves the cardinality of every occurrence edge. -/
theorem card_image_projection
    (B : HypergraphBundle J K H)
    {g : Finset K} (hg : g ∈ B.edges) :
    (g.image B.projection).card = g.card := by
  have hcard :=
    Fintype.card_congr (B.projectionEquiv hg)
  simpa using hcard.symm











/-- Under maximality, every factor in `maximalRemainderMainProduct` is
another factor of exactly the selected rank. -/
theorem card_eq_selected_of_mem_maximalRemainder
    (B : HypergraphBundle J K H)
    {g₀ g : Finset K}
    (hmax : ∀ f ∈ B.edges, f.card ≤ g₀.card)
    (hg :
      g ∈ (B.edges.erase g₀).filter
        (fun f => ¬ f.card < g₀.card)) :
    g.card = g₀.card := by
  have hg' := Finset.mem_filter.mp hg
  exact Nat.le_antisymm
    (hmax g (Finset.mem_of_mem_erase hg'.1))
    (Nat.le_of_not_gt hg'.2)





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
/-! ## Main-product cancellation at a selected edge -/

open Wikipedia.SzemeredisTheorem.HypergraphBundle in
/-- A same-rank density floor controls the entire maximal-rank remainder
product. -/
theorem solution
    (B : HypergraphBundle J K H)
    {g₀ : Finset K}
    (hmax : ∀ g ∈ B.edges, g.card ≤ g₀.card)
    (p : Finset J → ℝ) {a : ℝ}
    (ha : 0 ≤ a)
    (hp :
      ∀ e ∈ H, e.card = g₀.card →
        a ≤ p e) :
    a ^
          ((B.edges.erase g₀).filter
            (fun g => ¬ g.card < g₀.card)).card ≤
      B.maximalRemainderMainProduct g₀ p := by
  classical
  unfold maximalRemainderMainProduct
  calc
    a ^
          ((B.edges.erase g₀).filter
            (fun g => ¬ g.card < g₀.card)).card =
        ∏ _g ∈
            (B.edges.erase g₀).filter
              (fun g => ¬ g.card < g₀.card),
          a := by
      simp
    _ ≤
        ∏ g ∈
            (B.edges.erase g₀).filter
              (fun g => ¬ g.card < g₀.card),
          p (g.image B.projection) := by
      apply Finset.prod_le_prod
      · intro g hg
        exact ha
      · intro g hg
        apply hp _ (B.projection_mem_base g
          (Finset.mem_of_mem_erase
            (Finset.mem_filter.mp hg).1))
        rw [B.card_image_projection
          (Finset.mem_of_mem_erase
            (Finset.mem_filter.mp hg).1)]
        exact B.card_eq_selected_of_mem_maximalRemainder
          hmax hg
