-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_HypergraphBundle_doubledRemainderMoment_pullback_eq_duplicateOutside_bundleCount
-- name    : Wikipedia.SzemeredisTheorem.HypergraphBundle.doubledRemainderMoment_pullback_eq_duplicateOutside_bundleCount
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:32:59.442441+00:00
-- url     : https://prove2.me/theorems/249ecd40-ce77-41be-a003-86ae67db1e5f
-- title:
--   The doubled remainder moment is a duplicated bundle count
-- statement:
--   Let $B$ be a downward-closed hypergraph bundle with finite occurrence and value types, let $g_0$ be an edge of maximal cardinality, and let the base weights $A$ be idempotent. The doubled remainder moment at $g_0$ for the pulled-back weights equals the ordinary bundle count of the bundle duplicated outside $g_0$, with its corresponding pulled-back weights.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/HypergraphBundleIndicatorDuplication.lean#L363-L389

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleDuplication
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleIndicatorDuplication
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
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
open Wikipedia.SzemeredisTheorem.HypergraphBundle
variable {J K G : Type*}
  [DecidableEq J] [DecidableEq K]
  {H : Finset (Finset J)}

theorem Wikipedia.SzemeredisTheorem.HypergraphBundle.doubledRemainderMoment_pullback_eq_duplicateOutside_bundleCount
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    (hclosed : B.IsClosedUnderInclusion)
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges)
    (hmax : ∀ g ∈ B.edges, g.card ≤ g₀.card)
    (A : BaseEdgeWeight J G)
    (hA : BaseWeightsIdempotent H A) :
    B.doubledRemainderMoment g₀
        (B.pullbackBaseEdgeWeight A) =
      (B.duplicateOutside g₀).bundleCount
        ((B.duplicateOutside g₀).pullbackBaseEdgeWeight A) := by sorry
