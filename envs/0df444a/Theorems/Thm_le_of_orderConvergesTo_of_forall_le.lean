-- Prove2me | Theorems.Thm_le_of_orderConvergesTo_of_forall_le
-- name    : le_of_orderConvergesTo_of_forall_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:16:40.466878+00:00
-- url     : https://prove2.me/theorems/e6cab0c7-6a06-4914-a651-af32c8a6e87b
-- title:
--   le of order Converges To of forall le: le of order Converges To of forall le
-- statement:
--   If an order-convergent net is pointwise bounded above, then its limit is bounded above by
--   the same bound.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Convergences/Order.lean#L364-L368
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Convergences/Order.lean#L364-L368

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Basic
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Convergences_Order
set_option autoImplicit true
@[expose] public section
public section
universe u v
variable {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]

theorem le_of_orderConvergesTo_of_forall_le {ι : Type v} [Preorder ι]
    [IsDirected ι (· ≤ ·)] [Nonempty ι] {u : ι → X} {x b : X}
    (hu : OrderConvergesTo u x) (hub : ∀ i, u i ≤ b) :
    x ≤ b := by sorry
