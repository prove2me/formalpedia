-- Prove2me | Theorems.Thm_mme_Ctensor_outer_triple_distribution
-- name    : mme_Ctensor_outer_triple_distribution
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T11:23:26.118349+00:00
-- url     : https://prove2.me/theorems/cc2fc646-b24d-4d97-8388-7cc91f19c5ec
-- title:
--   Distribution of cyclic symmetrization over an outer C-tensor family
-- statement:
--   For a finite family of A order-three tensors, the cyclic symmetrization of their direct sum contains the direct sum of all A³ ordered heterogeneous cyclic products. Equivalently, distributing the three cyclic factors preserves every ordered outer triple.
-- source:
--   Distributive outer-family step in the Coppersmith-Winograd laser method and its asymmetric-hashing refinements.

import Mathlib.Data.Fintype.Card
import Definitions.Def_mme_cyclicSymmetrization_public_perm
import Definitions.Def_threeStarCyclicProduct
import Definitions.Def_mme_rank_bridge

open MME BigOperators

universe u

theorem mme_Ctensor_outer_triple_distribution
    {K : Type u} [Field K]
    {A : ℕ} (star : Fin A → TensorObj K 3) :
    let I := Fin A × Fin A × Fin A
    let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
    let block : Fin (Fintype.card I) → TensorObj K 3 := fun j =>
      let p := e.symm j
      threeStarCyclicProduct (star p.1) (star p.2.1) (star p.2.2)
    TensorObj.Restrict (TensorObj.bigAdd block)
      (cyclicSymmetrization (TensorObj.bigAdd star)) := by
  sorry
