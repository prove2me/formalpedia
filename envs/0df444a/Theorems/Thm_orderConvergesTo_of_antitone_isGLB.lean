-- Prove2me | Theorems.Thm_orderConvergesTo_of_antitone_isGLB
-- name    : orderConvergesTo_of_antitone_isGLB
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:16:37.25543+00:00
-- url     : https://prove2.me/theorems/22e227ed-6006-457a-a3ce-6a9d6f07c750
-- title:
--   order Converges To of antitone is GLB: order Converges To of antitone is GLB
-- statement:
--   A decreasing net order converges to its greatest lower bound.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Convergences/Order.lean#L162-L193
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Convergences/Order.lean#L162-L193

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Basic
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Convergences_Order
set_option autoImplicit true
@[expose] public section
public section
universe u v
variable {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]

theorem orderConvergesTo_of_antitone_isGLB {ι : Type v} [Preorder ι]
    [IsDirected ι (· ≤ ·)] [Nonempty ι] {u : ι → X} {x : X}
    (hanti : Antitone u) (hglb : IsGLB (Set.range u) x) :
    OrderConvergesTo u x := by sorry
