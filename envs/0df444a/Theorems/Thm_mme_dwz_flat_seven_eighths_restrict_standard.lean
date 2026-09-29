-- Prove2me | Theorems.Thm_mme_dwz_flat_seven_eighths_restrict_standard
-- name    : mme_dwz_flat_seven_eighths_restrict_standard
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T13:39:57.652468+00:00
-- url     : https://prove2.me/theorems/bd3c0376-658e-45c1-9835-2f39d758125b
-- title:
--   Flat-indexed Corollary-5.11 repair of many seven-eighths DWZ copies
-- statement:
--   Fix positive integers $N$ and $\ell$, put $g=8(N\ell+1)$, and consider a flat family of $kg$ broken copies of the DWZ Table-2 standard tensor. Suppose the useful small Z-block universe has cardinality at most $2^{N\ell}$ and every broken copy retains at least seven eighths of those blocks:
--
--   $$
--   7|B|\leq 8|H_r|.
--   $$
--
--   Then the flat direct sum of all broken sources restricts to a direct sum of $k$ complete standard tensors:
--
--   $$
--   \bigoplus_{a=1}^{k}D\leq\bigoplus_{r=1}^{kg}D[H_r].
--   $$
--
--   This flat-indexed form is the direct Corollary-5.11 adapter for the asymptotic extraction: it canonically groups the source family into $k$ groups of size $g$, applies one Hole-Lemma repair to each group, and assembles the repaired outputs.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 5.3, Definition 5.5, Lemma 5.6 and Corollary 5.11; Section 6.3, Claim 6.8 (seven-eighths nonhole estimate); https://arxiv.org/abs/2210.10173

import Theorems.Thm_mme_dwz_grouped_seven_eighths_restrict_standard

open BigOperators Finset
open MME Module PiTensorProduct
open MME.DWZSquare MME.DWZTable2StandardForm
open MME.DWZComponentRestriction

universe u

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 800000

theorem mme_dwz_flat_seven_eighths_restrict_standard
    (K : Type u) [Field K] (m N ell k : ℕ)
    (hN : 0 < N) (hell : 0 < ell)
    (copies : Fin (k * (8 * (N * ell + 1))) →
      BrokenBlockCopy (DWZStandardBlock m))
    (hcard : Fintype.card (DWZStandardBlock m) ≤ 2 ^ (N * ell))
    (hseven : ∀ r,
      7 * Fintype.card (DWZStandardBlock m) ≤
        8 * (copies r).nonholes.card) :
    let D : DWZStandardLabelledData K m :=
      { X := TensorObj.kronFin 15
          (fun r : Fin 15 ↦ restrictedComponentPower K r m)
        basis := TensorObj.kronFinModePiBasis 15
          (fun r : Fin 15 ↦ restrictedComponentPower K r m) 2
          (fun r ↦ restrictedComponentZBasis K r m)
        label := groupedUsefulBlock m }
    let G : Fin (k * (8 * (N * ell + 1))) → D.X.TypeGrading 2 :=
      fun r ↦ D.X.basisZAllowedGrading D.basis
        (fun W ↦ D.label W ∈ (copies r).nonholes)
    TensorObj.Restrict
      (TensorObj.bigAdd (fun _ : Fin k ↦ D.X))
      (TensorObj.bigAdd (fun r ↦
        (G r).blockSubtensor (fun _ ↦ 0))) := by
  sorry
