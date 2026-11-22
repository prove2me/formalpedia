-- Prove2me | Theorems.Thm_tendsto_of_orderConvergesTo_of_isOrderContinuousNorm
-- name    : tendsto_of_orderConvergesTo_of_isOrderContinuousNorm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:14:57.703948+00:00
-- url     : https://prove2.me/theorems/89759b5a-d745-419c-bf0c-d8f701b38147
-- title:
--   tendsto of order Converges To of is Order Continuous Norm: tendsto of order Converges To of is Order Continuous Norm
-- statement:
--   In a normed vector lattice with order-continuous norm, order convergence of a net implies
--   norm convergence.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/OrderContinuous/Basic.lean#L62-L88
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/OrderContinuous/Basic.lean#L62-L88

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Convergences_Order
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_OrderComplete
public import Definitions.Def_LeanPool_OrderClosures_BanLat_OrderContinuous_Basic
set_option autoImplicit true
@[expose] public section
public section
universe u
variable {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]

theorem tendsto_of_orderConvergesTo_of_isOrderContinuousNorm
    {X : Type u} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
    [NormedVectorLattice X] [IsOrderContinuousNorm X]
    {ι : Type u} [Preorder ι]
    {x : ι → X} {a : X} (hx : OrderConvergesTo x a) :
    Filter.Tendsto x Filter.atTop (nhds a) := by sorry
