-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_HypergraphBundle_pullbackBaseEdgeWeight_duplicateOutside_doubledEdge
-- name    : Wikipedia.SzemeredisTheorem.HypergraphBundle.pullbackBaseEdgeWeight_duplicateOutside_doubledEdge
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:33:06.6492+00:00
-- url     : https://prove2.me/theorems/4b91fabc-c922-491d-be8f-5c7c3ac2a607
-- title:
--   Pullback weights agree on lifted occurrence edges
-- statement:
--   Let $B$ be a hypergraph bundle, let $g_0$ be a finite vertex set, and let $A$ be base edge weights. For any edge $g\in B.\mathrm{edges}\setminus\{g_0\}$, either Boolean copy, and doubled assignment $x$, the pulled-back weight on the lifted edge in the duplicated bundle equals the original pulled-back weight on $g$ evaluated at the corresponding lifted vertex values.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/HypergraphBundleIndicatorDuplication.lean#L159-L276

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

theorem Wikipedia.SzemeredisTheorem.HypergraphBundle.pullbackBaseEdgeWeight_duplicateOutside_doubledEdge
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (A : BaseEdgeWeight J G)
    (copy : Bool) {g : Finset K}
    (hg : g ∈ B.edges.erase g₀)
    (x : DoubledOccurrenceVertex g₀ → G) :
    (B.duplicateOutside g₀).pullbackBaseEdgeWeight A
        (doubledEdge g₀ copy g)
        (edgeTuple (doubledEdge g₀ copy g) x) =
      B.pullbackBaseEdgeWeight A g
        (fun v => x (doubledVertexLift g₀ copy v.1)) := by sorry
