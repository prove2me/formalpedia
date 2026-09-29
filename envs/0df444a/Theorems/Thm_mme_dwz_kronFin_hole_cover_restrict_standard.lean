-- Prove2me | Theorems.Thm_mme_dwz_kronFin_hole_cover_restrict_standard
-- name    : mme_dwz_kronFin_hole_cover_restrict_standard
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T12:31:28.34672+00:00
-- url     : https://prove2.me/theorems/68a0d0d7-bab2-48f4-bafa-92799ca97bb0
-- title:
--   The exact-once Hole Lemma restricts onto the literal fifteen-factor DWZ standard tensor
-- statement:
--   Fix a field and the literal fifteen-factor Kronecker DWZ standard tensor. Let a finite family of broken copies retain subsets of useful blocks. If the useful-block universe has size at most $2^{N\ell}$ and the sum of the copies' nonhole fractions is at least $N\ell+1$, then the direct sum of the corresponding broken standard subtensors restricts onto the complete literal fifteen-factor standard tensor. This is the exact tensor-level conclusion of the Hole Lemma: the target is the original standard tensor itself, not merely the formal sum of its labelled pieces.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Hole Lemma and the standard-tensor block repair in Section 5, especially Definition 5.5 and the covering argument on PDF pp. 47--50 / printed pp. 46--49; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_standard_labelled_z_blocks
import Definitions.Def_mme_dwz_restricted_component_z_basis
import Definitions.Def_mme_kronFin_mode_pi_basis

open BigOperators Finset
open MME Module PiTensorProduct
open MME.DWZSquare MME.DWZTable2StandardForm
open MME.DWZComponentRestriction

universe u

set_option autoImplicit false

theorem mme_dwz_kronFin_hole_cover_restrict_standard
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
    TensorObj.Restrict D.X
      (TensorObj.bigAdd
        (fun t ↦ (G t).blockSubtensor (fun _ ↦ 0))) := by
  sorry
