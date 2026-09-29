-- Prove2me | Theorems.Thm_mme_dwz_grouped_seven_eighths_restrict_standard
-- name    : mme_dwz_grouped_seven_eighths_restrict_standard
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T13:30:41.276654+00:00
-- url     : https://prove2.me/theorems/47ca750b-3682-4cc4-9fde-b45de515b5f2
-- title:
--   Fixed-size Corollary-5.11 repair of many seven-eighths DWZ copies
-- statement:
--   Fix positive integers $N$ and $\ell$, and set $g=8(N\ell+1)$. Consider $k$ groups of $g$ broken copies of the DWZ Table-2 standard tensor. Suppose the number of useful small Z-blocks in that standard form is at most $2^{N\ell}$, and every broken copy retains at least seven eighths of those blocks, in the division-free form
--
--   $$
--   7|B|\leq 8|H_{a,b}|.
--   $$
--
--   Then the flat direct sum of all $kg$ broken sources restricts to the direct sum of $k$ complete standard tensors:
--
--   $$
--   \bigoplus_{a=1}^{k}D\leq\bigoplus_{a=1}^{k}\bigoplus_{b=1}^{g}D[H_{a,b}].
--   $$
--
--   Here $D[H_{a,b}]$ denotes the basis-graded subtensor retaining exactly the useful blocks in the nonhole set $H_{a,b}$. The factor-eight group size gives the Hole Lemma total nonhole threshold with constant-factor slack. This is a source-faithful fixed-size specialization of the amplification in Corollary 5.11.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 5.3, Definition 5.5, Lemma 5.6 and Corollary 5.11; Section 6.3, Claim 6.8 (seven-eighths nonhole estimate); https://arxiv.org/abs/2210.10173

import Theorems.Thm_mme_bigAdd_fin_mul_grouped_restrict
import Theorems.Thm_mme_dwz_nonholeFraction_seven_eighths
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

theorem mme_dwz_grouped_seven_eighths_restrict_standard
    (K : Type u) [Field K] (m N ell k : ℕ)
    (hN : 0 < N) (hell : 0 < ell)
    (copies : Fin k → Fin (8 * (N * ell + 1)) →
      BrokenBlockCopy (DWZStandardBlock m))
    (hcard : Fintype.card (DWZStandardBlock m) ≤ 2 ^ (N * ell))
    (hseven : ∀ a b,
      7 * Fintype.card (DWZStandardBlock m) ≤
        8 * (copies a b).nonholes.card) :
    let D : DWZStandardLabelledData K m :=
      { X := TensorObj.kronFin 15
          (fun r : Fin 15 ↦ restrictedComponentPower K r m)
        basis := TensorObj.kronFinModePiBasis 15
          (fun r : Fin 15 ↦ restrictedComponentPower K r m) 2
          (fun r ↦ restrictedComponentZBasis K r m)
        label := groupedUsefulBlock m }
    let G : Fin k → Fin (8 * (N * ell + 1)) → D.X.TypeGrading 2 :=
      fun a b ↦ D.X.basisZAllowedGrading D.basis
        (fun W ↦ D.label W ∈ (copies a b).nonholes)
    TensorObj.Restrict
      (TensorObj.bigAdd (fun _ : Fin k ↦ D.X))
      (TensorObj.bigAdd
        (fun r : Fin (k * (8 * (N * ell + 1))) ↦
          (G (finProdFinEquiv.symm r).1
              (finProdFinEquiv.symm r).2).blockSubtensor (fun _ ↦ 0))) := by
  sorry
