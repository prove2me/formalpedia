-- Prove2me | Theorems.Thm_orderConvergesTo_const
-- name    : orderConvergesTo_const
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:11:03.688265+00:00
-- url     : https://prove2.me/theorems/d247fae0-1f6e-46b3-bffc-9d79c7014332
-- title:
--   order Converges To const: order Converges To const
-- statement:
--   A constant net order converges to its constant value.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Convergences/Order.lean#L37-L49
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Convergences/Order.lean#L37-L49

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Basic
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Convergences_Order
set_option autoImplicit true
@[expose] public section
public section
universe u v
variable {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]

theorem orderConvergesTo_const {ι : Type v} [Preorder ι]
     (x : X) :
    OrderConvergesTo (fun _ : ι => x) x := by sorry
