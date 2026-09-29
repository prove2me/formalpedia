-- Prove2me | Theorems.Thm_mme_dwz_flat_aggregate_groups_restrict_standard
-- name    : mme_dwz_flat_aggregate_groups_restrict_standard
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T19:40:39.56654+00:00
-- url     : https://prove2.me/theorems/d805052b-3e29-4c70-a46a-9e0f076b9749
-- title:
--   Variable-size aggregate Hole groups repair a flat DWZ family
-- statement:
--   Let a flat family of broken DWZ standard tensors be divided into consecutive, possibly different-sized groups followed by an unused remainder. Suppose every group has aggregate normalized nonhole mass at least $N\ell+1$, and the finite standard-block universe has cardinality at most $2^{N\ell}$. Then the direct sum of one complete DWZ standard tensor for every group is a restriction of the original flat direct sum, with the remainder discarded. This is the variable-width, paper-faithful form of the Hole-Lemma amplification used in Corollary 5.11; it requires only aggregate mass within each group and no pointwise $7/8$ condition.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Lemma 5.6 and Corollary 5.11; https://arxiv.org/abs/2210.10173

import Theorems.Thm_mme_bigAdd_list_flatten_isomorphic_nested
import Theorems.Thm_mme_bigAdd_list_prefix_restrict
import Theorems.Thm_mme_bigAdd_mono_restrict
import Theorems.Thm_mme_dwz_kronFin_hole_cover_restrict_standard
import Theorems.Thm_mme_dwz_table2_exact_outer_profile_usefulBlock_nonempty

open BigOperators Finset
open MME Module PiTensorProduct
open MME.DWZSquare MME.DWZTable2StandardForm
open MME.DWZComponentRestriction

universe u

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 800000

theorem mme_dwz_flat_aggregate_groups_restrict_standard
    (K : Type u) [Field K] (m N ell : ℕ)
    (hN : 0 < N) (hell : 0 < ell)
    (groups : List (List (BrokenBlockCopy (DWZStandardBlock m))))
    (remainder : List (BrokenBlockCopy (DWZStandardBlock m)))
    (hcard : Fintype.card (DWZStandardBlock m) ≤ 2 ^ (N * ell))
    (haggregate : ∀ group ∈ groups,
      ((N * ell + 1 : ℕ) : ℝ) ≤
        (group.map nonholeFraction).sum) :
    let D : DWZStandardLabelledData K m :=
      { X := TensorObj.kronFin 15
          (fun r : Fin 15 ↦ restrictedComponentPower K r m)
        basis := TensorObj.kronFinModePiBasis 15
          (fun r : Fin 15 ↦ restrictedComponentPower K r m) 2
          (fun r ↦ restrictedComponentZBasis K r m)
        label := groupedUsefulBlock m }
    let G : BrokenBlockCopy (DWZStandardBlock m) → D.X.TypeGrading 2 :=
      fun copy ↦ D.X.basisZAllowedGrading D.basis
        (fun W ↦ D.label W ∈ copy.nonholes)
    TensorObj.Restrict
      (TensorObj.bigAdd (fun _ : Fin groups.length ↦ D.X))
      (TensorObj.bigAdd (fun r : Fin (groups.flatten ++ remainder).length ↦
        (G ((groups.flatten ++ remainder).get r)).blockSubtensor
          (fun _ ↦ 0))) := by
  sorry
