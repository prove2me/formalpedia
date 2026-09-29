-- Prove2me | solution 1 for Erdos146.booleanWordOnes_card_equiv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T05:14:58.942125+00:00
-- url     : https://prove2.me/submissions/37296213-ac92-4632-ae4a-46cc2471b4ce

import Definitions.Def_erdos146_core2
import Mathlib.Data.Finset.Card

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem solution
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (equivalence : ι ≃ κ)
    (word : κ → Bool) :
    (booleanWordOnes (fun index : ι => word (equivalence index))).card =
      (booleanWordOnes word).card := by
  classical
  apply Finset.card_bij
    (fun index _ => equivalence index)
  · intro index hindex
    have hone := (Finset.mem_filter.mp hindex).2
    unfold booleanWordOnes
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hone⟩
  · intro first _ second _ hequal
    exact equivalence.injective hequal
  · intro index hindex
    refine ⟨equivalence.symm index, ?_, equivalence.apply_symm_apply index⟩
    unfold booleanWordOnes
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have hone := (Finset.mem_filter.mp hindex).2
    simpa using hone
