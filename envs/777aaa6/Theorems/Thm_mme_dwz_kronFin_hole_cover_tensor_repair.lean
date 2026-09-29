-- Prove2me | Theorems.Thm_mme_dwz_kronFin_hole_cover_tensor_repair
-- name    : mme_dwz_kronFin_hole_cover_tensor_repair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T12:05:39.977614+00:00
-- url     : https://prove2.me/theorems/ae038173-53a0-4e02-9f71-6615156258d5
-- title:
--   Exact-once tensor repair of a finite family of broken Table-2 copies
-- statement:
--   Fix a finite family of broken DWZ Table-2 standard tensors. Suppose the useful-block universe has cardinality at most $2^{N\ell}$ and the sum of the copies' nonhole fractions is at least $N\ell+1$, with $N,\ell>0$. Then there is a genuine tensor restriction
--
--   $$
--   \bigoplus_t T_{\mathrm{broken},t}\longrightarrow\sum_b T_b,
--   $$
--
--   where the target contains every useful-block contribution exactly once. The construction chooses uniform grouped-position shuffles, assigns each useful block to one covering copy, and applies a third-mode owner projection after the common shuffle.
--
--   This is the complete finite tensor-realization form of the Hole Lemma used in the asymmetric-hashing square analysis; only the source-specific construction of the copies and quantitative nonhole bound remain upstream.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Lemma 5.6 and Claims 5.8--5.10, especially the exact repair of broken tensors in the proof of Claim 5.9; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_standard_labelled_z_blocks
import Definitions.Def_mme_dwz_restricted_component_z_basis
import Definitions.Def_mme_kronFin_mode_pi_basis

open BigOperators Finset
open MME Module PiTensorProduct
open MME.DWZSquare MME.DWZTable2StandardForm
open MME.DWZComponentRestriction

universe u

set_option autoImplicit false

theorem mme_dwz_kronFin_hole_cover_tensor_repair
    (K : Type u) [Field K] (m N ell : ℕ) {s : ℕ}
    (hN : 0 < N) (hell : 0 < ell)
    (copies : Fin s → BrokenBlockCopy (DWZStandardBlock m))
    (hcard : Fintype.card (DWZStandardBlock m) ≤ 2 ^ (N * ell))
    (hsum : ((N * ell + 1 : ℕ) : ℝ) ≤
      ∑ t : Fin s, nonholeFraction (copies t)) :
    let D : DWZStandardLabelledData K m :=
      { X := TensorObj.kronFin 15
          (fun r : Fin 15 ↦ restrictedComponentPower K r m)
        basis := TensorObj.kronFinModePiBasis 15
          (fun r : Fin 15 ↦ restrictedComponentPower K r m) 2
          (fun r ↦ restrictedComponentZBasis K r m)
        label := groupedUsefulBlock m }
    let G : Fin s → D.X.TypeGrading 2 := fun t ↦
      D.X.basisZAllowedGrading D.basis
        (fun W ↦ D.label W ∈ (copies t).nonholes)
    TensorObj.Restrict
      ({ V := D.X.V
         t := ∑ block : DWZStandardBlock m,
           dwzLabelledUsefulBlockTensor K m D block } : TensorObj K 3)
      (TensorObj.bigAdd
        (fun t ↦ (G t).blockSubtensor (fun _ ↦ 0))) := by
  sorry
