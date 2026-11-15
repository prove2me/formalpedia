-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.abs_bundleCount_pullback_sub_bundleMainProduct_le_envelope
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:27:05.645718+00:00
-- url     : https://prove2.me/submissions/20e32aab-9d9a-49af-92bd-cf7ab38d533f

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_HypergraphBundle_bundleCount_eq_bundleMainProduct_of_order_zero
import Theorems.Thm_Wikipedia_SzemeredisTheorem_HypergraphBundle_bundleMainProduct_duplicateOutside_lowerOrder
import Theorems.Thm_Wikipedia_SzemeredisTheorem_HypergraphBundle_bundleMainProduct_lowerOrder_eq_boundary_mul_exterior
import Theorems.Thm_Wikipedia_SzemeredisTheorem_HypergraphBundle_card_duplicateOutside_lowerOrder_le
import Theorems.Thm_Wikipedia_SzemeredisTheorem_HypergraphBundle_duplicateOutside_lowerOrder_closed
import Theorems.Thm_Wikipedia_SzemeredisTheorem_HypergraphBundle_eraseEdge_closed_of_maximal
import Theorems.Thm_Wikipedia_SzemeredisTheorem_HypergraphBundle_exists_edge_card_eq_order
import Theorems.Thm_Wikipedia_SzemeredisTheorem_HypergraphBundle_lowerOrder_mul_maximalRemainder_eq_erase_main
import Theorems.Thm_Wikipedia_SzemeredisTheorem_HypergraphBundle_pow_card_edges_le_bundleMainProduct_of_edges
import Theorems.Thm_Wikipedia_SzemeredisTheorem_HypergraphBundle_pow_card_edges_le_selected_mul_maximalRemainder

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



@[simp]
theorem eraseEdge_edges
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    (B.eraseEdge g₀).edges = B.edges.erase g₀ :=
  rfl

/-- Erasing an edge cannot increase bundle order. -/
theorem eraseEdge_order_le
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    (B.eraseEdge g₀).order ≤ B.order := by
  unfold order eraseEdge
  apply Finset.sup_le
  intro g hg
  exact B.edge_card_le_order (Finset.mem_of_mem_erase hg)





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

/-- Pullback preserves unit-interval bounds on every bundle edge. -/
theorem pullbackBaseEdgeWeight_unitInterval
    (B : HypergraphBundle J K H)
    (A : BaseEdgeWeight J G)
    (hA : BaseWeightsInUnitInterval H A)
    {g : Finset K} (hg : g ∈ B.edges)
    (y : {v : K // v ∈ g} → G) :
    0 ≤ B.pullbackBaseEdgeWeight A g y ∧
      B.pullbackBaseEdgeWeight A g y ≤ 1 := by
  rw [B.pullbackBaseEdgeWeight_of_mem A hg y]
  exact hA _ (B.projection_mem_base g hg) _

/-! ## Bundle products and normalized counts -/



/-- Pulling back a bounded base family gives a bounded bundle family. -/
theorem pullbackBaseEdgeWeight_weightsInUnitInterval
    (B : HypergraphBundle J K H)
    (A : BaseEdgeWeight J G)
    (hA : BaseWeightsInUnitInterval H A) :
    B.WeightsInUnitInterval
      (B.pullbackBaseEdgeWeight A) := by
  intro g hg y
  exact B.pullbackBaseEdgeWeight_unitInterval A hA hg y





theorem bundleProduct_nonneg
    (B : HypergraphBundle J K H)
    {A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ}
    (hA : B.WeightsInUnitInterval A)
    (x : K → G) :
    0 ≤ B.bundleProduct A x := by
  unfold bundleProduct
  exact Finset.prod_nonneg fun g hg =>
    (hA g hg (edgeTuple g x)).1



theorem bundleCount_nonneg
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    {A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ}
    (hA : B.WeightsInUnitInterval A) :
    0 ≤ B.bundleCount A :=
  mean_nonneg (B.bundleProduct_nonneg hA)















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









/-- A fixed-copy lift is injective. -/
theorem doubledVertexLift_injective
    (g₀ : Finset K) (copy : Bool) :
    Function.Injective (doubledVertexLift g₀ copy) := by
  intro v w hvw
  have h :=
    congrArg (doubledVertexForget g₀) hvw
  simpa using h



















/-- Lifting preserves edge cardinality. -/
@[simp]
theorem card_doubledEdge
    (g₀ : Finset K) (copy : Bool) (g : Finset K) :
    (doubledEdge g₀ copy g).card = g.card := by
  rw [doubledEdge,
    Finset.card_image_of_injective _
      (doubledVertexLift_injective g₀ copy)]































@[simp]
theorem duplicateOutside_edges
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    (B.duplicateOutside g₀).edges =
      B.doubledEdges g₀ :=
  rfl



/-- Every doubled edge has the cardinality of the source edge which
produced it. -/
theorem duplicateOutside_edge_card
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    {d : Finset (DoubledOccurrenceVertex g₀)}
    (hd : d ∈ (B.duplicateOutside g₀).edges) :
    ∃ g ∈ B.edges.erase g₀, d.card = g.card := by
  obtain ⟨copy, g, hg, hgd⟩ :=
    (B.mem_doubledEdges_iff g₀ d).1 hd
  subst d
  exact ⟨g, hg, card_doubledEdge g₀ copy g⟩

/-- Duplication does not increase bundle order. -/
theorem duplicateOutside_order_le_eraseEdge
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    (B.duplicateOutside g₀).order ≤
      (B.eraseEdge g₀).order := by
  unfold order
  apply Finset.sup_le
  intro d hd
  obtain ⟨g, hg, hdg⟩ :=
    B.duplicateOutside_edge_card g₀ hd
  rw [hdg]
  exact (B.eraseEdge g₀).edge_card_le_order hg

/-- In particular, duplication does not increase the original order. -/
theorem duplicateOutside_order_le
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    (B.duplicateOutside g₀).order ≤ B.order :=
  (B.duplicateOutside_order_le_eraseEdge g₀).trans
    (B.eraseEdge_order_le g₀)























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











/-- Edge filtering cannot increase the number of occurrence edges. -/
theorem card_filterEdges_edges_le
    (B : HypergraphBundle J K H)
    (P : Finset K → Prop) [DecidablePred P] :
    (B.filterEdges P).edges.card ≤ B.edges.card := by
  exact Finset.card_le_card (Finset.filter_subset _ _)

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



/-- For a positive cutoff, every edge in the lower-order subbundle has
order strictly below that cutoff, including when the subbundle is empty. -/
theorem lowerOrder_order_lt
    (B : HypergraphBundle J K H)
    {d : ℕ} (hd : 0 < d) :
    (B.lowerOrder d).order < d := by
  unfold order
  rw [Finset.sup_lt_iff hd]
  intro g hg
  exact (Finset.mem_filter.mp hg).2









@[simp]
theorem strictBoundary_edges
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    (B.strictBoundary g₀).edges =
      B.edges.filter fun g => g ⊂ g₀ :=
  rfl





/-- A strict boundary has order below the size of its ambient edge. -/
theorem strictBoundary_order_lt
    (B : HypergraphBundle J K H)
    {g₀ : Finset K} (hg₀ : g₀.Nonempty) :
    (B.strictBoundary g₀).order < g₀.card := by
  unfold order
  rw [Finset.sup_lt_iff (Finset.card_pos.mpr hg₀)]
  intro g hg
  exact Finset.card_lt_card (Finset.mem_filter.mp hg).2

theorem card_strictBoundary_edges_le
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    (B.strictBoundary g₀).edges.card ≤ B.edges.card :=
  B.card_filterEdges_edges_le _

theorem strictBoundary_closed
    (B : HypergraphBundle J K H)
    (hclosed : B.IsClosedUnderInclusion)
    (g₀ : Finset K) :
    (B.strictBoundary g₀).IsClosedUnderInclusion := by
  apply B.filterEdges_closed _ hclosed
  intro g hg f hfg
  exact Finset.ssubset_of_subset_of_ssubset hfg hg

/-! ## Main-density products -/











/-- Erasing one edge removes precisely its main-density factor. -/
theorem bundleMainProduct_eraseEdge_mul
    (B : HypergraphBundle J K H)
    (p : Finset J → ℝ)
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges) :
    (B.eraseEdge g₀).bundleMainProduct p *
        p (g₀.image B.projection) =
      B.bundleMainProduct p := by
  classical
  unfold bundleMainProduct
  simp only [eraseEdge]
  rw [Finset.prod_erase_mul _ _ hg₀]

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





















/-! ## Main-product cancellation at a selected edge -/





/-- Projection preserves the cardinality of every occurrence edge. -/
theorem card_image_projection
    (B : HypergraphBundle J K H)
    {g : Finset K} (hg : g ∈ B.edges) :
    (g.image B.projection).card = g.card := by
  have hcard :=
    Fintype.card_congr (B.projectionEquiv hg)
  simpa using hcard.symm



/-- Nonnegative base densities give a nonnegative bundle main product. -/
theorem bundleMainProduct_nonneg
    (B : HypergraphBundle J K H)
    (p : Finset J → ℝ)
    (hp : ∀ e ∈ H, 0 ≤ p e) :
    0 ≤ B.bundleMainProduct p := by
  unfold bundleMainProduct
  exact Finset.prod_nonneg fun g hg =>
    hp _ (B.projection_mem_base g hg)



/-- The strict-boundary factor in the localized defect and the main
product of the duplicated lower-order bundle form the square of the full
lower-order main product.  This is the cancellation which prevents the
defect estimate from paying every lower-rank density a second time. -/
theorem boundary_mul_duplicateLower_main_eq_lowerOrder_sq
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (p : Finset J → ℝ) :
    (B.strictBoundary g₀).bundleMainProduct p *
        ((B.lowerOrder g₀.card).duplicateOutside g₀).bundleMainProduct p =
      ((B.lowerOrder g₀.card).bundleMainProduct p) ^ 2 := by
  rw [B.bundleMainProduct_duplicateOutside_lowerOrder
    g₀ p]
  rw [Finset.prod_pow]
  rw [B.bundleMainProduct_lowerOrder_eq_boundary_mul_exterior
    g₀ p]
  unfold lowerExteriorMainProduct
  ring









/-! ## Discarding the other maximal-rank factors -/











end HypergraphBundle

/-! ## Numerical envelope for the double induction -/





/-- Restatement of the envelope recurrence using the named increment. -/
theorem IsBundleCountingEnvelope.add_stepIncrement_le
    {α β μ : ℕ → ℝ} {τ : ℝ}
    {E : ℕ → ℕ → ℝ}
    (hE : IsBundleCountingEnvelope α β μ τ E)
    (d n : ℕ) :
    E (d + 1) n +
        bundleCountingStepIncrement α β μ τ E d n ≤
      E (d + 1) (n + 1) := by
  simpa [bundleCountingStepIncrement, add_assoc] using hE.step d n

/-- Both lower-order correction factors in the envelope are nonnegative. -/
theorem IsBundleCountingEnvelope.lower_correction_nonneg
    {α β μ : ℕ → ℝ} {τ : ℝ}
    {E : ℕ → ℕ → ℝ}
    (hE : IsBundleCountingEnvelope α β μ τ E)
    (d n : ℕ) :
    0 ≤
      (1 + E d (n + 1)) *
        (1 + E d (2 * (n + 1))) := by
  exact mul_nonneg
    (by linarith [hE.error_nonneg d (n + 1)])
    (by linarith [hE.error_nonneg d (2 * (n + 1))])

end Wikipedia.SzemeredisTheorem

end

section


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

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

namespace HypergraphBundle

variable {J K G : Type*}
  [DecidableEq J] [DecidableEq K]
  {H : Finset (Finset J)}

/-! ## Canonical pullbacks on subbundles -/







/-! ## Structural bounds for the two outer-induction bundles -/



/-- Duplicating the lower-order subbundle still has order strictly below
the selected edge. -/
theorem duplicateOutside_lowerOrder_order_lt
    (B : HypergraphBundle J K H)
    {g₀ : Finset K} (hg₀ : g₀.Nonempty) :
    ((B.lowerOrder g₀.card).duplicateOutside g₀).order <
      g₀.card := by
  exact
    ((B.lowerOrder g₀.card).duplicateOutside_order_le
      g₀).trans_lt
      (B.lowerOrder_order_lt
        (Finset.card_pos.mpr hg₀))



/-! ## Elementary main-product and induction helpers -/



/-- A relative absolute-error estimate gives the corresponding upper
bound for the count. -/
theorem count_le_one_add_error_mul_main
    {count main error : ℝ}
    (herror : |count - main| ≤ error * main) :
    count ≤ (1 + error) * main := by
  have hleft : count - main ≤ |count - main| :=
    le_abs_self _
  calc
    count ≤ main + |count - main| := by
      linarith
    _ ≤ main + error * main :=
      add_le_add_right herror main
    _ = (1 + error) * main := by
      ring







end HypergraphBundle

/-! ## The analytic one-edge interface -/

universe uJ uG

variable {J : Type uJ} {G : Type uG}
  [DecidableEq J] [Fintype G] [DecidableEq G]
  {H : Finset (Finset J)}



/-! ## Full double induction -/



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
/-! ## The analytic one-edge interface -/
universe uJ uG
variable {J : Type uJ} {G : Type uG}
  [DecidableEq J] [Fintype G] [DecidableEq G]
  {H : Finset (Finset J)}
/-! ## Full double induction -/

open Wikipedia.SzemeredisTheorem in
omit [DecidableEq G] in
/-- **Relative generalized bundle counting.**  A source-faithful
maximal-edge analytic step and a numerical envelope control every closed
bundle, uniformly in its occurrence-vertex type. -/
theorem solution
    [Nonempty G]
    (A : HypergraphBundle.BaseEdgeWeight J G)
    (p : Finset J → ℝ)
    (α β μ : ℕ → ℝ) (τ : ℝ)
    (E : ℕ → ℕ → ℝ)
    (hA01 :
      HypergraphBundle.BaseWeightsInUnitInterval H A)
    (_hAidempotent :
      HypergraphBundle.BaseWeightsIdempotent H A)
    (hAempty :
      ∀ y :
        {j : J // j ∈ (∅ : Finset J)} → G,
        A ∅ y = 1)
    (hpempty : p ∅ = 1)
    (hpLower :
      ∀ e ∈ H, α e.card ≤ p e)
    (hstep :
      HasTaoBundleCountingStep
        (H := H) A p β τ)
    (hE :
      IsBundleCountingEnvelope α β μ τ E)
    {K : Type} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle J K H)
    (hclosed : B.IsClosedUnderInclusion) :
    |B.bundleCount (B.pullbackBaseEdgeWeight A) -
        B.bundleMainProduct p| ≤
      E B.order B.edges.card *
        B.bundleMainProduct p := by
  let P : ℕ → ℕ → Prop :=
    fun d n =>
      ∀ (K' : Type) [Fintype K'] [DecidableEq K']
        (C : HypergraphBundle J K' H),
        C.order ≤ d →
        C.edges.card ≤ n →
        C.IsClosedUnderInclusion →
        |C.bundleCount (C.pullbackBaseEdgeWeight A) -
            C.bundleMainProduct p| ≤
          E d n * C.bundleMainProduct p
  have hp0 :
      ∀ e ∈ H, 0 ≤ p e := by
    intro e he
    exact (hE.density_pos e.card).le.trans
      (hpLower e he)
  unfold HasTaoBundleCountingStep at hstep
  have hP : ∀ d n, P d n := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ihOrder =>
        intro n
        induction n using Nat.strong_induction_on with
        | h n ihCard =>
            dsimp [P]
            intro K' _instK' _decK' C hCd hCn hclosedC
            by_cases horderEq : C.order = d
            · by_cases hcardEq : C.edges.card = n
              · by_cases hd0 : d = 0
                · have hzero : C.order = 0 :=
                    horderEq.trans hd0
                  have hexact :=
                    C.bundleCount_eq_bundleMainProduct_of_order_zero
                      A p hAempty hpempty hzero
                  rw [hexact, sub_self, abs_zero]
                  exact mul_nonneg
                    (hE.error_nonneg d n)
                    (C.bundleMainProduct_nonneg p hp0)
                · have hdpos : 0 < d :=
                    Nat.pos_of_ne_zero hd0
                  obtain ⟨g₀, hg₀, hgcard, hmax⟩ :=
                    C.exists_edge_card_eq_order
                      (horderEq.symm ▸ hdpos)
                  have hgcardD : g₀.card = d :=
                    hgcard.trans horderEq
                  have hg₀ne : g₀.Nonempty := by
                    apply Finset.card_pos.mp
                    rw [hgcardD]
                    exact hdpos
                  obtain ⟨d₀, rfl⟩ :=
                    Nat.exists_eq_succ_of_ne_zero hd0
                  have hn0 : n ≠ 0 := by
                    intro hn
                    have hcardzero : C.edges.card = 0 :=
                      hcardEq.trans hn
                    exact
                      (Finset.card_ne_zero.mpr
                        ⟨g₀, hg₀⟩) hcardzero
                  obtain ⟨n₀, rfl⟩ :=
                    Nat.exists_eq_succ_of_ne_zero hn0
                  let Cerase := C.eraseEdge g₀
                  let Cboundary := C.strictBoundary g₀
                  let Clower :=
                    (C.lowerOrder g₀.card).duplicateOutside g₀
                  have hCeraseClosed :
                      Cerase.IsClosedUnderInclusion :=
                    C.eraseEdge_closed_of_maximal
                      hclosedC hg₀ hmax
                  have hCeraseOrder :
                      Cerase.order ≤ d₀ + 1 := by
                    exact
                      (C.eraseEdge_order_le g₀).trans_eq
                        horderEq
                  have hCeraseCard :
                      Cerase.edges.card ≤ n₀ := by
                    have hcard :
                        Cerase.edges.card = n₀ := by
                      simp [Cerase,
                        Finset.card_erase_of_mem hg₀,
                        hcardEq]
                    exact hcard.le
                  have hEraseIH :=
                    (ihCard n₀ (Nat.lt_succ_self n₀))
                      K' Cerase hCeraseOrder
                        hCeraseCard hCeraseClosed
                  have hCboundaryClosed :
                      Cboundary.IsClosedUnderInclusion :=
                    C.strictBoundary_closed hclosedC g₀
                  have hCboundaryOrder :
                      Cboundary.order ≤ d₀ := by
                    have hlt :
                        Cboundary.order < d₀ + 1 := by
                      simpa [Cboundary, hgcardD,
                        Nat.succ_eq_add_one] using
                        C.strictBoundary_order_lt hg₀ne
                    omega
                  have hCboundaryCard :
                      Cboundary.edges.card ≤ n₀ + 1 := by
                    exact
                      (C.card_strictBoundary_edges_le g₀).trans_eq
                        hcardEq
                  have hBoundaryIH :=
                    (ihOrder d₀ (Nat.lt_succ_self d₀)
                      (n₀ + 1))
                      K' Cboundary hCboundaryOrder
                        hCboundaryCard hCboundaryClosed
                  have hClowerClosed :
                      Clower.IsClosedUnderInclusion := by
                    dsimp [Clower]
                    exact C.duplicateOutside_lowerOrder_closed
                      hclosedC g₀
                  have hClowerOrder :
                      Clower.order ≤ d₀ := by
                    have hlt :
                        Clower.order < d₀ + 1 := by
                      simpa [Clower, hgcardD,
                        Nat.succ_eq_add_one] using
                        C.duplicateOutside_lowerOrder_order_lt
                          hg₀ne
                    omega
                  have hClowerCard :
                      Clower.edges.card ≤
                        2 * (n₀ + 1) := by
                    dsimp [Clower]
                    exact
                      (C.card_duplicateOutside_lowerOrder_le
                        g₀).trans_eq
                        (congrArg (fun m => 2 * m)
                          hcardEq)
                  have hLowerIH :=
                    (ihOrder d₀ (Nat.lt_succ_self d₀)
                      (2 * (n₀ + 1)))
                      (HypergraphBundle.DoubledOccurrenceVertex g₀)
                      Clower hClowerOrder
                        hClowerCard hClowerClosed
                  let mainErase :=
                    Cerase.bundleMainProduct p
                  let mainBoundary :=
                    Cboundary.bundleMainProduct p
                  let mainLower :=
                    Clower.bundleMainProduct p
                  let mainLowerOrder :=
                    (C.lowerOrder g₀.card).bundleMainProduct p
                  let mainMax :=
                    C.maximalRemainderMainProduct g₀ p
                  let mainC := C.bundleMainProduct p
                  let countErase :=
                    Cerase.bundleCount
                      (Cerase.pullbackBaseEdgeWeight A)
                  let countBoundary :=
                    Cboundary.bundleCount
                      (Cboundary.pullbackBaseEdgeWeight A)
                  let countLower :=
                    Clower.bundleCount
                      (Clower.pullbackBaseEdgeWeight A)
                  let p₀ :=
                    p (g₀.image C.projection)
                  have hmainErase0 : 0 ≤ mainErase := by
                    dsimp [mainErase, Cerase]
                    exact
                      (C.eraseEdge g₀).bundleMainProduct_nonneg p hp0
                  have hmainBoundary0 :
                      0 ≤ mainBoundary := by
                    dsimp [mainBoundary, Cboundary]
                    exact
                      (C.strictBoundary g₀).bundleMainProduct_nonneg p hp0
                  have hmainLower0 :
                      0 ≤ mainLower := by
                    dsimp [mainLower, Clower]
                    exact
                      ((C.lowerOrder g₀.card).duplicateOutside g₀).bundleMainProduct_nonneg
                        p hp0
                  have hmainLowerOrder0 :
                      0 ≤ mainLowerOrder := by
                    dsimp [mainLowerOrder]
                    exact
                      (C.lowerOrder g₀.card).bundleMainProduct_nonneg p hp0
                  have hmainC0 : 0 ≤ mainC := by
                    dsimp [mainC]
                    exact C.bundleMainProduct_nonneg p hp0
                  have hcountBoundary0 :
                      0 ≤ countBoundary := by
                    dsimp [countBoundary, Cboundary]
                    exact
                      (C.strictBoundary g₀).bundleCount_nonneg
                        ((C.strictBoundary g₀).pullbackBaseEdgeWeight_weightsInUnitInterval
                            A hA01)
                  have hcountLower0 :
                      0 ≤ countLower := by
                    dsimp [countLower, Clower]
                    exact
                      ((C.lowerOrder g₀.card).duplicateOutside g₀).bundleCount_nonneg
                          (HypergraphBundle.pullbackBaseEdgeWeight_weightsInUnitInterval
                            ((C.lowerOrder g₀.card).duplicateOutside g₀) A hA01)
                  have hcountBoundary :
                      countBoundary ≤
                        (1 + E d₀ (n₀ + 1)) *
                          mainBoundary :=
                    HypergraphBundle.count_le_one_add_error_mul_main
                      hBoundaryIH
                  have hcountLower :
                      countLower ≤
                        (1 + E d₀
                            (2 * (n₀ + 1))) *
                          mainLower :=
                    HypergraphBundle.count_le_one_add_error_mul_main
                      hLowerIH
                  have hcorrection0 :
                      0 ≤
                        (1 + E d₀ (n₀ + 1)) *
                          (1 + E d₀
                            (2 * (n₀ + 1))) :=
                    hE.lower_correction_nonneg d₀ n₀
                  have hfirstCorrection0 :
                      0 ≤ 1 + E d₀ (n₀ + 1) := by
                    linarith
                      [hE.error_nonneg d₀ (n₀ + 1)]
                  have hβ0 :
                      0 ≤ β (d₀ + 1) :=
                    hE.defect_nonneg _
                  have hradicand :
                      β (d₀ + 1) *
                            countBoundary * countLower ≤
                        β (d₀ + 1) *
                            ((1 + E d₀ (n₀ + 1)) *
                              mainBoundary) *
                          ((1 + E d₀
                              (2 * (n₀ + 1))) *
                            mainLower) := by
                    calc
                      β (d₀ + 1) *
                            countBoundary * countLower ≤
                          β (d₀ + 1) *
                              ((1 + E d₀ (n₀ + 1)) *
                                mainBoundary) *
                            countLower :=
                        mul_le_mul_of_nonneg_right
                          (mul_le_mul_of_nonneg_left
                            hcountBoundary hβ0)
                          hcountLower0
                      _ ≤
                          β (d₀ + 1) *
                              ((1 + E d₀ (n₀ + 1)) *
                                mainBoundary) *
                            ((1 + E d₀
                                (2 * (n₀ + 1))) *
                              mainLower) :=
                        mul_le_mul_of_nonneg_left
                          hcountLower
                          (mul_nonneg hβ0
                            (mul_nonneg
                              hfirstCorrection0
                              hmainBoundary0))
                  let rootCorrection :=
                    Real.sqrt
                      (β (d₀ + 1) *
                        (1 + E d₀ (n₀ + 1)) *
                        (1 + E d₀
                          (2 * (n₀ + 1))))
                  have hrootCorrection0 :
                      0 ≤ rootCorrection :=
                    Real.sqrt_nonneg _
                  have hmainBoundaryLower :
                      mainBoundary * mainLower =
                        mainLowerOrder ^ 2 := by
                    dsimp [mainBoundary, mainLower,
                      mainLowerOrder, Cboundary, Clower]
                    exact
                      C.boundary_mul_duplicateLower_main_eq_lowerOrder_sq
                        g₀ p
                  have hcoefficient0 :
                      0 ≤
                        β (d₀ + 1) *
                          (1 + E d₀ (n₀ + 1)) *
                          (1 + E d₀
                            (2 * (n₀ + 1))) := by
                    rw [mul_assoc]
                    exact mul_nonneg hβ0 hcorrection0
                  have hsqrt :
                      Real.sqrt
                            (β (d₀ + 1) *
                              countBoundary * countLower) ≤
                        rootCorrection * mainLowerOrder := by
                    calc
                      Real.sqrt
                            (β (d₀ + 1) *
                              countBoundary * countLower) ≤
                          Real.sqrt
                            (β (d₀ + 1) *
                              ((1 + E d₀ (n₀ + 1)) *
                                mainBoundary) *
                              ((1 + E d₀
                                  (2 * (n₀ + 1))) *
                                mainLower)) :=
                        Real.sqrt_le_sqrt hradicand
                      _ =
                          Real.sqrt
                              ((β (d₀ + 1) *
                                  (1 + E d₀ (n₀ + 1)) *
                                  (1 + E d₀
                                    (2 * (n₀ + 1)))) *
                                (mainBoundary * mainLower)) := by
                        congr 1
                        ring
                      _ =
                          Real.sqrt
                              ((β (d₀ + 1) *
                                  (1 + E d₀ (n₀ + 1)) *
                                  (1 + E d₀
                                    (2 * (n₀ + 1)))) *
                                mainLowerOrder ^ 2) := by
                        congr 1
                        rw [hmainBoundaryLower]
                      _ = rootCorrection * mainLowerOrder := by
                        dsimp [rootCorrection]
                        rw [Real.sqrt_mul hcoefficient0]
                        rw [Real.sqrt_sq hmainLowerOrder0]
                  have hαp :
                      α (d₀ + 1) ^ (n₀ + 1) ≤
                        p₀ * mainMax := by
                    dsimp [p₀, mainMax]
                    have hpow :=
                      C.pow_card_edges_le_selected_mul_maximalRemainder
                        hg₀ hmax p
                        (hE.density_pos g₀.card).le
                        (hE.density_le_one g₀.card)
                        (fun e he hcard =>
                          hpLower e he |>
                            fun h => by
                              simpa [hcard] using h)
                    simpa [hgcardD, hcardEq,
                      Nat.succ_eq_add_one] using hpow
                  have hαpowpos :
                      0 < α (d₀ + 1) ^ (n₀ + 1) :=
                    pow_pos (hE.density_pos _) _
                  have hmainFactor :
                      mainLowerOrder * (p₀ * mainMax) =
                        mainC := by
                    dsimp [mainLowerOrder, p₀, mainMax,
                      mainC, Cerase]
                    calc
                      (C.lowerOrder g₀.card).bundleMainProduct p *
                          (p (g₀.image C.projection) *
                            C.maximalRemainderMainProduct
                              g₀ p) =
                          ((C.lowerOrder g₀.card).bundleMainProduct p *
                            C.maximalRemainderMainProduct
                              g₀ p) *
                            p (g₀.image C.projection) := by
                        ring
                      _ =
                          (C.eraseEdge g₀).bundleMainProduct p *
                            p (g₀.image C.projection) := by
                        rw [
                          C.lowerOrder_mul_maximalRemainder_eq_erase_main
                            g₀ p]
                      _ = C.bundleMainProduct p :=
                        C.bundleMainProduct_eraseEdge_mul
                          p hg₀
                  have hsqrtNormalized :
                      Real.sqrt
                            (β (d₀ + 1) *
                              countBoundary * countLower) ≤
                        (rootCorrection /
                            α (d₀ + 1) ^ (n₀ + 1)) *
                          mainC := by
                    have hscaled :
                        rootCorrection ≤
                          (rootCorrection /
                              α (d₀ + 1) ^ (n₀ + 1)) *
                            (p₀ * mainMax) := by
                      calc
                        rootCorrection =
                            (rootCorrection /
                              α (d₀ + 1) ^ (n₀ + 1)) *
                              α (d₀ + 1) ^ (n₀ + 1) := by
                          field_simp
                        _ ≤
                            (rootCorrection /
                              α (d₀ + 1) ^ (n₀ + 1)) *
                              (p₀ * mainMax) :=
                          mul_le_mul_of_nonneg_left hαp
                            (div_nonneg hrootCorrection0
                              hαpowpos.le)
                    calc
                      Real.sqrt
                            (β (d₀ + 1) *
                              countBoundary * countLower) ≤
                          rootCorrection * mainLowerOrder :=
                        hsqrt
                      _ ≤
                          ((rootCorrection /
                              α (d₀ + 1) ^ (n₀ + 1)) *
                            (p₀ * mainMax)) *
                              mainLowerOrder :=
                        mul_le_mul_of_nonneg_right
                          hscaled hmainLowerOrder0
                      _ =
                          (rootCorrection /
                              α (d₀ + 1) ^ (n₀ + 1)) *
                            mainC := by
                        rw [← hmainFactor]
                        ring
                  have hμmain :
                      μ (d₀ + 1) ^ (n₀ + 1) ≤
                        mainC := by
                    dsimp [mainC]
                    have hpow :=
                      C.pow_card_edges_le_bundleMainProduct_of_edges
                        p (hE.floor_pos (d₀ + 1)).le
                        (fun g hg => by
                          have hcard :
                              g.card ≤ d₀ + 1 := by
                            exact
                              (C.edge_card_le_order hg).trans_eq
                                (by
                                  simpa [Nat.succ_eq_add_one] using
                                    horderEq)
                          exact
                            (hE.rankFloor hcard).trans
                              (hpLower _
                                (C.projection_mem_base g hg) |>
                                  fun h => by
                                    simpa [C.card_image_projection hg]
                                      using h))
                    simpa [hcardEq] using hpow
                  have hμpowpos :
                      0 < μ (d₀ + 1) ^ (n₀ + 1) :=
                    pow_pos (hE.floor_pos _) _
                  have huniformNormalized :
                      τ ≤
                        (τ /
                            μ (d₀ + 1) ^ (n₀ + 1)) *
                          mainC := by
                    calc
                      τ =
                          (τ /
                            μ (d₀ + 1) ^ (n₀ + 1)) *
                              μ (d₀ + 1) ^ (n₀ + 1) := by
                        field_simp
                      _ ≤
                          (τ /
                            μ (d₀ + 1) ^ (n₀ + 1)) *
                            mainC :=
                        mul_le_mul_of_nonneg_left hμmain
                          (div_nonneg hE.uniform_nonneg
                            hμpowpos.le)
                  have hstepRaw :=
                    hstep K' C hclosedC hg₀ hmax
                  have hstepNormalized :
                      |C.bundleCount
                              (C.pullbackBaseEdgeWeight A) -
                            p₀ * countErase| ≤
                        (rootCorrection /
                              α (d₀ + 1) ^ (n₀ + 1) +
                            τ /
                              μ (d₀ + 1) ^ (n₀ + 1)) *
                          mainC := by
                    calc
                      |C.bundleCount
                              (C.pullbackBaseEdgeWeight A) -
                            p₀ * countErase| ≤
                          Real.sqrt
                              (β (d₀ + 1) *
                                countBoundary * countLower) +
                            τ := by
                        simpa [p₀, countErase,
                          countBoundary, countLower,
                          Cerase, Cboundary, Clower,
                          hgcardD] using hstepRaw
                      _ ≤
                          (rootCorrection /
                              α (d₀ + 1) ^ (n₀ + 1)) *
                              mainC +
                            (τ /
                              μ (d₀ + 1) ^ (n₀ + 1)) *
                              mainC :=
                        add_le_add hsqrtNormalized
                          huniformNormalized
                      _ =
                          (rootCorrection /
                                α (d₀ + 1) ^ (n₀ + 1) +
                              τ /
                                μ (d₀ + 1) ^ (n₀ + 1)) *
                            mainC := by
                        ring
                  have hp₀0 : 0 ≤ p₀ := by
                    dsimp [p₀]
                    exact hp0 _
                      (C.projection_mem_base g₀ hg₀)
                  have hmainEraseFactor :
                      p₀ * mainErase = mainC := by
                    dsimp [p₀, mainErase, mainC,
                      Cerase]
                    rw [mul_comm]
                    exact
                      C.bundleMainProduct_eraseEdge_mul
                        p hg₀
                  have hEraseNormalized :
                      p₀ *
                          |countErase - mainErase| ≤
                        E (d₀ + 1) n₀ * mainC := by
                    calc
                      p₀ *
                            |countErase - mainErase| ≤
                          p₀ *
                            (E (d₀ + 1) n₀ *
                              mainErase) :=
                        mul_le_mul_of_nonneg_left
                          hEraseIH hp₀0
                      _ =
                          E (d₀ + 1) n₀ * mainC := by
                        rw [← hmainEraseFactor]
                        ring
                  have hdecompose :
                      C.bundleCount
                            (C.pullbackBaseEdgeWeight A) -
                          mainC =
                        (C.bundleCount
                              (C.pullbackBaseEdgeWeight A) -
                            p₀ * countErase) +
                          p₀ * (countErase - mainErase) := by
                    rw [← hmainEraseFactor]
                    ring
                  rw [hdecompose]
                  calc
                    |(C.bundleCount
                              (C.pullbackBaseEdgeWeight A) -
                            p₀ * countErase) +
                          p₀ * (countErase - mainErase)| ≤
                        |C.bundleCount
                              (C.pullbackBaseEdgeWeight A) -
                            p₀ * countErase| +
                          |p₀ * (countErase - mainErase)| :=
                      abs_add_le _ _
                    _ =
                        |C.bundleCount
                              (C.pullbackBaseEdgeWeight A) -
                            p₀ * countErase| +
                          p₀ * |countErase - mainErase| := by
                      rw [abs_mul, abs_of_nonneg hp₀0]
                    _ ≤
                        (rootCorrection /
                              α (d₀ + 1) ^ (n₀ + 1) +
                            τ /
                              μ (d₀ + 1) ^ (n₀ + 1)) *
                            mainC +
                          E (d₀ + 1) n₀ * mainC :=
                      add_le_add hstepNormalized
                        hEraseNormalized
                    _ =
                        (E (d₀ + 1) n₀ +
                            (rootCorrection /
                                α (d₀ + 1) ^ (n₀ + 1) +
                              τ /
                                μ (d₀ + 1) ^ (n₀ + 1))) *
                          mainC := by
                      ring
                    _ ≤
                        E (d₀ + 1) (n₀ + 1) *
                          mainC := by
                      apply mul_le_mul_of_nonneg_right
                      · simpa [rootCorrection,
                          bundleCountingStepIncrement,
                          add_assoc] using
                          hE.add_stepIncrement_le d₀ n₀
                      · exact hmainC0
              · have hcardLt : C.edges.card < n :=
                  lt_of_le_of_ne hCn
                    hcardEq
                have hsmall :=
                  (ihCard C.edges.card hcardLt)
                    K' C hCd le_rfl hclosedC
                have hmain0 :
                    0 ≤ C.bundleMainProduct p :=
                  C.bundleMainProduct_nonneg p hp0
                exact hsmall.trans
                  (mul_le_mul_of_nonneg_right
                    (hE.error_mono_card hCn) hmain0)
            · have horderLt : C.order < d :=
                lt_of_le_of_ne hCd
                  horderEq
              have hsmall :=
                (ihOrder C.order horderLt n)
                  K' C le_rfl hCn hclosedC
              have hmain0 :
                  0 ≤ C.bundleMainProduct p :=
                C.bundleMainProduct_nonneg p hp0
              exact hsmall.trans
                (mul_le_mul_of_nonneg_right
                  (hE.error_mono_order hCd) hmain0)
  exact
    (hP B.order B.edges.card)
      K B le_rfl le_rfl hclosed
