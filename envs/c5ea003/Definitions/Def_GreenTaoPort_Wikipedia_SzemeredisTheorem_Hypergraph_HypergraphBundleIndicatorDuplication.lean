-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleIndicatorDuplication
-- name    : GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleIndicatorDuplication
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T05:51:09.839333+00:00
-- url     : https://prove2.me/theorems/62d501a6-65ca-4d55-89f3-40b9a921c51c
-- title:
--   Idempotent base weights and edge factors on duplicated bundles
-- statement:
--   A base-edge weight family is idempotent on a base hypergraph when $A_e(y)^2=A_e(y)$ for every base edge and assignment. Real zero–one indicator families satisfy this condition.
--
--   The bundle also supplies the membership-subtype equivalence induced by equality of two finite sets, and the weight of an actual edge in a duplicated occurrence bundle at a fixed doubled assignment. The latter uses the duplicated bundle's projection to pull back the original base-edge weights. These definitions keep exact finite-edge identities available during the indicator-duplication argument.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/HypergraphBundleIndicatorDuplication.lean#L24-L286

import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleDuplication
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Indicator weights on a duplicated hypergraph bundle

The source-indexed doubled product retains both labelled copies of every
remaining occurrence edge.  The ordinary duplicated bundle instead stores
the image of the source-edge map, so it identifies the two copies of an edge
contained in the shared edge.  For pulled-back zero--one base weights this
identification does not change the product: the only lost multiplicity is a
repeated idempotent factor.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

namespace HypergraphBundle

variable {J K G : Type*}
  [DecidableEq J] [DecidableEq K]
  {H : Finset (Finset J)}

/-- Pointwise idempotence of a base-edge weight family on the base
hypergraph.  Real-valued indicator families satisfy this condition. -/
def BaseWeightsIdempotent
    (H : Finset (Finset J))
    (A : BaseEdgeWeight J G) : Prop :=
  ∀ e ∈ H, ∀ y, A e y * A e y = A e y

/-- Equality of finite sets transports their membership subtypes. -/
def finsetMembershipEquivOfEq
    {α : Type*} {s t : Finset α} (h : s = t) :
    {a : α // a ∈ s} ≃ {a : α // a ∈ t} :=
  Equiv.cast
    (congrArg (fun u : Finset α => {a : α // a ∈ u}) h)













/-- The weight of an actual doubled occurrence edge at a fixed doubled
assignment. -/
noncomputable def doubledBundleEdgeFactor
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (A : BaseEdgeWeight J G)
    (x : DoubledOccurrenceVertex g₀ → G)
    (d : Finset (DoubledOccurrenceVertex g₀)) : ℝ :=
  (B.duplicateOutside g₀).pullbackBaseEdgeWeight A d
    (edgeTuple d x)









end HypergraphBundle

end Wikipedia.SzemeredisTheorem


