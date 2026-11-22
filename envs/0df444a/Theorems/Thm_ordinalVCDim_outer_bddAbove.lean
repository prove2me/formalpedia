-- Prove2me | Theorems.Thm_ordinalVCDim_outer_bddAbove
-- name    : ordinalVCDim_outer_bddAbove
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:32:58.449638+00:00
-- url     : https://prove2.me/theorems/3d1ac12e-69bf-410c-a027-2fe24d3597ae
-- title:
--   ordinal VCDim outer bdd Above: ordinal VCDim outer bdd Above
-- statement:
--   Outer BddAbove: the range of the full OrdinalVCDim iSup is bounded by ω.
--       Holds for all concept classes regardless of whether VCDim is finite or infinite.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Ordinal.lean#L45-L52
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Ordinal.lean#L45-L52

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

theorem ordinalVCDim_outer_bddAbove (X : Type u) (C : ConceptClass X Bool) :
    BddAbove (Set.range (fun S : Finset X =>
      ⨆ (_ : Shatters X C S), ((S.card : ℕ) : Ordinal))) := by sorry
