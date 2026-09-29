-- Prove2me | Theorems.Thm_mme_bigAdd_list_flatten_isomorphic_nested
-- name    : mme_bigAdd_list_flatten_isomorphic_nested
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T19:27:07.813375+00:00
-- url     : https://prove2.me/theorems/7717515e-914e-4920-a7a9-2eed368402f7
-- title:
--   Variable-width finite tensor direct sums flatten canonically
-- statement:
--   Let a finite list of tensor summands be partitioned into a finite list of groups, whose sizes may vary. The direct sum indexed by the flattened list is isomorphic to the direct sum over groups of the direct sum within each group.
--
--   This is the variable-width reindexing needed after greedy aggregate-mass grouping: it changes only the association and indexing of summands, with no loss of tensors or quantitative mass.
-- source:
--   Finite direct-sum reindexing used to formalize the variable-sized grouping step in Duan--Wu--Zhou, Faster Matrix Multiplication via Asymmetric Hashing, Corollary 5.11.

import Definitions.Def_mme_rank_bridge

open MME BigOperators

universe u v

set_option autoImplicit false

theorem mme_bigAdd_list_flatten_isomorphic_nested
    {K : Type u} [Field K] {d : ℕ} {Item : Type v}
    (groups : List (List Item)) (X : Item → TensorObj K d) :
    TensorObj.Isomorphic
      (TensorObj.bigAdd (fun r : Fin groups.flatten.length ↦
        X (groups.flatten.get r)))
      (TensorObj.bigAdd (fun a : Fin groups.length ↦
        TensorObj.bigAdd (fun b : Fin (groups.get a).length ↦
          X ((groups.get a).get b)))) := by
  sorry
