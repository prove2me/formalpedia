-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.HypergraphBundle.pow_card_edges_le_selected_mul_maximalRemainder
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:21:01.400348+00:00
-- url     : https://prove2.me/submissions/c0259be5-cd5e-4fa7-b343-16281baff43d

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_HypergraphBundle_pow_card_maximalRemainder_le

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













/-- The number of other selected-rank edges is at most the number of
edges left after erasing the selected one. -/
theorem card_maximalRemainder_le_erase
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    ((B.edges.erase g₀).filter
      (fun g => ¬ g.card < g₀.card)).card ≤
        (B.edges.erase g₀).card :=
  Finset.card_le_card (Finset.filter_subset _ _)



/-! ## Discarding the other maximal-rank factors -/











end HypergraphBundle

/-! ## Numerical envelope for the double induction -/









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
/-- The selected density together with all other selected-rank densities
is bounded below by one floor factor per edge of the original bundle. -/
theorem solution
    (B : HypergraphBundle J K H)
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges)
    (hmax : ∀ g ∈ B.edges, g.card ≤ g₀.card)
    (p : Finset J → ℝ) {a : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hp :
      ∀ e ∈ H, e.card = g₀.card →
        a ≤ p e) :
    a ^ B.edges.card ≤
      p (g₀.image B.projection) *
        B.maximalRemainderMainProduct g₀ p := by
  let s :=
    (B.edges.erase g₀).filter
      (fun g => ¬ g.card < g₀.card)
  have hscard :
      s.card ≤ (B.edges.erase g₀).card :=
    B.card_maximalRemainder_le_erase g₀
  have hpmax :
      a ^ s.card ≤
        B.maximalRemainderMainProduct g₀ p :=
    B.pow_card_maximalRemainder_le
      hmax p ha0 hp
  have hpow :
      a ^ (B.edges.erase g₀).card ≤
        a ^ s.card :=
    pow_le_pow_of_le_one ha0 ha1 hscard
  have hremain :
      a ^ (B.edges.erase g₀).card ≤
        B.maximalRemainderMainProduct g₀ p :=
    hpow.trans hpmax
  have hselected :
      a ≤ p (g₀.image B.projection) := by
    apply hp _ (B.projection_mem_base g₀ hg₀)
    exact B.card_image_projection hg₀
  have hselected0 :
      0 ≤ p (g₀.image B.projection) :=
    ha0.trans hselected
  calc
    a ^ B.edges.card =
        a * a ^ (B.edges.erase g₀).card := by
      rw [← Finset.card_erase_add_one hg₀,
        pow_succ, mul_comm]
    _ ≤
        p (g₀.image B.projection) *
          a ^ (B.edges.erase g₀).card :=
      mul_le_mul_of_nonneg_right hselected
        (pow_nonneg ha0 _)
    _ ≤
        p (g₀.image B.projection) *
          B.maximalRemainderMainProduct g₀ p :=
      mul_le_mul_of_nonneg_left hremain hselected0
