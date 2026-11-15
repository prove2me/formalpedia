-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleGeneralizedCounting
-- name    : GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleGeneralizedCounting
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T08:52:04.1782+00:00
-- url     : https://prove2.me/theorems/23fc1055-2e80-4b4a-a2be-758290ff91ba
-- title:
--   Local bundle products and quantitative counting envelopes
-- statement:
--   A tuple on a selected occurrence edge restricts to any subedge. The strict-boundary local product uses these restrictions to multiply all proper-subedge factors. Idempotence requires each used occurrence weight to satisfy $A^2=A$.
--
--   Two main-density products separate lower-rank edges outside the selected edge from the erased edges that are not strictly lower rank. Under maximality the latter are the other edges of the selected rank.
--
--   A counting-envelope certificate records positive density floors, nonnegative defect and uniformity errors, and an error function monotone in bundle order and edge count. Its successor inequality absorbs the previous erased-edge error, a square-root localized-defect term involving two lower-order calls, and a uniformity term divided by a common density floor. The one-step increment is supplied separately with exactly these density-power normalizations.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/HypergraphBundleGeneralizedCounting.lean#L39-L775

import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleIndicatorDuplication
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleFiltration
import Lean
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


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

/-- Restrict a tuple on `g` to a subedge `f`. -/
def restrictEdgeTuple
    {f g : Finset K} (hfg : f ⊆ g)
    (y : {v : K // v ∈ g} → G) :
    {v : K // v ∈ f} → G :=
  fun v => y ⟨v.1, hfg v.2⟩



/-- Product of all strict-boundary occurrence-edge weights, viewed as a
function of a tuple on the selected edge.  The subtype index retains the
proof that every factor really is a strict subedge of `g₀`. -/
noncomputable def strictBoundaryLocalProduct
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    (y : {v : K // v ∈ g₀} → G) : ℝ :=
  ∏ g :
      {g : Finset K //
        g ∈ (B.strictBoundary g₀).edges},
    A g.1
      (restrictEdgeTuple
        (((B.mem_strictBoundary_edges g₀ g.1).1
          g.2).2.1)
        y)





/-- Pointwise idempotence of an occurrence-edge weight family. -/
def WeightsIdempotent
    (B : HypergraphBundle J K H)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ) : Prop :=
  ∀ g ∈ B.edges, ∀ y,
    A g y * A g y = A g y









/-! ## Main-product cancellation at a selected edge -/

/-- Product of the lower-order main densities which do not lie in the
selected edge. -/
noncomputable def lowerExteriorMainProduct
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (p : Finset J → ℝ) : ℝ :=
  ∏ g ∈ B.edges.filter
      (fun g =>
        g.card < g₀.card ∧ ¬ g ⊆ g₀),
    p (g.image B.projection)

/-- Product of the main densities on the erased edges which are not
strictly lower than the selected edge.  Under maximality these are exactly
the other edges of the selected rank. -/
noncomputable def maximalRemainderMainProduct
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (p : Finset J → ℝ) : ℝ :=
  ∏ g ∈ (B.edges.erase g₀).filter
      (fun g => ¬ g.card < g₀.card),
    p (g.image B.projection)



















/-! ## Discarding the other maximal-rank factors -/











end HypergraphBundle

/-! ## Numerical envelope for the double induction -/

/-- A quantitative envelope for Tao's double induction on bundle order
and bundle size.

The recurrence has three pieces:

* the error already accumulated after erasing the selected edge;
* the localized defect error, controlled by two lower-order bundle calls;
* the common frozen-uniformity error.

The field `rankFloor` says that `μ d` is a common lower bound for every
density at rank at most `d`. -/
structure IsBundleCountingEnvelope
    (α β μ : ℕ → ℝ) (τ : ℝ)
    (E : ℕ → ℕ → ℝ) : Prop where
  density_pos : ∀ d, 0 < α d
  density_le_one : ∀ d, α d ≤ 1
  defect_nonneg : ∀ d, 0 ≤ β d
  uniform_nonneg : 0 ≤ τ
  floor_pos : ∀ d, 0 < μ d
  rankFloor :
    ∀ ⦃i d : ℕ⦄, i ≤ d → μ d ≤ α i
  error_nonneg :
    ∀ d n, 0 ≤ E d n
  error_mono_order :
    ∀ ⦃d d' n : ℕ⦄, d ≤ d' →
      E d n ≤ E d' n
  error_mono_card :
    ∀ ⦃d n n' : ℕ⦄, n ≤ n' →
      E d n ≤ E d n'
  step :
    ∀ d n,
      E (d + 1) n +
            Real.sqrt
                (β (d + 1) *
                  (1 + E d (n + 1)) *
                  (1 + E d (2 * (n + 1)))) /
              (α (d + 1)) ^ (n + 1) +
          τ / (μ (d + 1)) ^ (n + 1) ≤
        E (d + 1) (n + 1)

/-- The one-step increment appearing in a bundle-counting envelope. -/
noncomputable def bundleCountingStepIncrement
    (α β μ : ℕ → ℝ) (τ : ℝ)
    (E : ℕ → ℕ → ℝ)
    (d n : ℕ) : ℝ :=
  Real.sqrt
        (β (d + 1) *
          (1 + E d (n + 1)) *
          (1 + E d (2 * (n + 1)))) /
      (α (d + 1)) ^ (n + 1) +
    τ / (μ (d + 1)) ^ (n + 1)





end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.bundleCountingStepIncrement.eq_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


