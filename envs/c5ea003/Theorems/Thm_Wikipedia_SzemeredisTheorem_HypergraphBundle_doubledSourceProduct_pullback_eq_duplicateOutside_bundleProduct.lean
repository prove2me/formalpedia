-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_HypergraphBundle_doubledSourceProduct_pullback_eq_duplicateOutside_bundleProduct
-- name    : Wikipedia.SzemeredisTheorem.HypergraphBundle.doubledSourceProduct_pullback_eq_duplicateOutside_bundleProduct
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:32:58.713217+00:00
-- url     : https://prove2.me/theorems/a3924ff1-ac4d-423a-9cd2-3f51ef2c4e2f
-- title:
--   Idempotent base weights identify doubled and duplicated products
-- statement:
--   For any hypergraph bundle $B$, finite vertex set $g_0$, and idempotent base weights $A$, the doubled source product with pulled-back weights equals the bundle product of the bundle duplicated outside $g_0$ at every doubled assignment.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/HypergraphBundleIndicatorDuplication.lean#L321-L361

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

theorem Wikipedia.SzemeredisTheorem.HypergraphBundle.doubledSourceProduct_pullback_eq_duplicateOutside_bundleProduct
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (A : BaseEdgeWeight J G)
    (hA : BaseWeightsIdempotent H A)
    (x : DoubledOccurrenceVertex g₀ → G) :
    B.doubledSourceProduct g₀
        (B.pullbackBaseEdgeWeight A) x =
      (B.duplicateOutside g₀).bundleProduct
        ((B.duplicateOutside g₀).pullbackBaseEdgeWeight A) x := by sorry
