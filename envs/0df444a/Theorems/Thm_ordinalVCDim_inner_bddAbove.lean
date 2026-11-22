-- Prove2me | Theorems.Thm_ordinalVCDim_inner_bddAbove
-- name    : ordinalVCDim_inner_bddAbove
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:32:55.885747+00:00
-- url     : https://prove2.me/theorems/aba67e26-0454-4d7a-bebe-117b650bfcee
-- title:
--   ordinal VCDim inner bdd Above: ordinal VCDim inner bdd Above
-- statement:
--   Inner BddAbove: for a fixed S, the range over shattering witnesses is trivially bounded.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Ordinal.lean#L38-L41
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Ordinal.lean#L38-L41

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Littlestone
public import Mathlib.SetTheory.Ordinal.Basic
public import Mathlib.Algebra.Order.Module.Field
public import Mathlib.Data.EReal.Inv
public import Mathlib.SetTheory.Ordinal.Arithmetic
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.MetricSpace.Bounded
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Ordinal
set_option autoImplicit true
@[expose] public section
public section
universe u v

theorem ordinalVCDim_inner_bddAbove (X : Type u) (C : ConceptClass X Bool)
    (S : Finset X) :
    BddAbove (Set.range (fun (_ : Shatters X C S) => ((S.card : ℕ) : Ordinal))) := by sorry
