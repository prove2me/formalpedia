-- Prove2me | Theorems.Thm_mme_dwz_grouped_aggregate_restrict_standard
-- name    : mme_dwz_grouped_aggregate_restrict_standard
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T18:50:54.951951+00:00
-- url     : https://prove2.me/theorems/5c95139a-2a6e-4a57-86c6-c7e9a5fd4432
-- title:
--   DWZ Hole Lemma grouping from aggregate non-hole mass
-- statement:
--   Let a level-$\ell$ DWZ standard tensor have at most $2^{N\ell}$ available small $Z$-blocks. For each of $k$ groups, suppose there are $g$ broken copies whose non-hole fractions $\eta_{a,b}$ satisfy
--
--   $$
--   N\ell+1 \le \sum_{b<g} \eta_{a,b}.
--   $$
--
--   Then the direct sum of all $kg$ allowed-block subtensors restricts to a direct sum of $k$ complete standard tensors.
--
--   This is the groupwise, tensor-restriction interface to the DWZ Hole Lemma. It preserves the aggregate quantifier used by the probabilistic argument and does not require a separate lower bound for every broken copy.
--
--   **Formalization Note** The finite product equivalence reindexes the $k\times g$ family into `Fin (k * g)`.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5 / FOCS 2023, Lemma 5.6 and Corollary 5.11 (printed pp. 48-49 / PDF pp. 49-50).

import Theorems.Thm_mme_bigAdd_fin_mul_grouped_restrict
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

theorem mme_dwz_grouped_aggregate_restrict_standard
    (K : Type u) [Field K] (m N ell k g : ℕ)
    (hN : 0 < N) (hell : 0 < ell)
    (copies : Fin k → Fin g → BrokenBlockCopy (DWZStandardBlock m))
    (hcard : Fintype.card (DWZStandardBlock m) ≤ 2 ^ (N * ell))
    (haggregate : ∀ a,
      ((N * ell + 1 : ℕ) : ℝ) ≤
        ∑ b : Fin g, nonholeFraction (copies a b)) :
    let D : DWZStandardLabelledData K m :=
      { X := TensorObj.kronFin 15
          (fun r : Fin 15 ↦ restrictedComponentPower K r m)
        basis := TensorObj.kronFinModePiBasis 15
          (fun r : Fin 15 ↦ restrictedComponentPower K r m) 2
          (fun r ↦ restrictedComponentZBasis K r m)
        label := groupedUsefulBlock m }
    let G : Fin k → Fin g → D.X.TypeGrading 2 :=
      fun a b ↦ D.X.basisZAllowedGrading D.basis
        (fun W ↦ D.label W ∈ (copies a b).nonholes)
    TensorObj.Restrict
      (TensorObj.bigAdd (fun _ : Fin k ↦ D.X))
      (TensorObj.bigAdd
        (fun r : Fin (k * g) ↦
          (G (finProdFinEquiv.symm r).1
              (finProdFinEquiv.symm r).2).blockSubtensor (fun _ ↦ 0))) := by
  sorry
