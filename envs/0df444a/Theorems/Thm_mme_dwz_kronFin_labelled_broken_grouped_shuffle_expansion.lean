-- Prove2me | Theorems.Thm_mme_dwz_kronFin_labelled_broken_grouped_shuffle_expansion
-- name    : mme_dwz_kronFin_labelled_broken_grouped_shuffle_expansion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T11:55:35.019184+00:00
-- url     : https://prove2.me/theorems/0b331b39-33bd-4259-b99d-a6397494d9c6
-- title:
--   Exact grouped-shuffle expansion of a broken Table-2 tensor in literal Kronecker coordinates
-- statement:
--   Write the complete DWZ Table-2 standard tensor as the ordered Kronecker product of its fifteen restricted component powers, with its third-mode product basis labelled by useful blocks. For any broken copy and any grouped position shuffle $g$, there are modewise linear maps whose action is
--
--   $$
--   F_g(T_{\mathrm{broken}})=\sum_b \mathbf 1_{\{g^{-1}b\text{ is a nonhole}\}}T_b.
--   $$
--
--   Thus the broken tensor is transported to exactly the relabelled nonhole useful-block contributions required by the owner-selection step of the Hole Lemma.
--
--   **Formalization Note** The statement exposes the same literal fifteen-factor `kronFin` object and product basis used by the proved grouped automorphism, avoiding elaborator-intensive unfolding of an opaque notational wrapper.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definition 5.7 and Claims 5.8--5.10, especially the common shuffle and broken-tensor expansion in the proof of Claim 5.9; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_standard_labelled_z_blocks
import Definitions.Def_mme_dwz_restricted_component_z_basis
import Definitions.Def_mme_kronFin_mode_pi_basis
import Definitions.Def_mme_dwz_table2_useful_block_shuffle_action

open BigOperators Finset
open MME Module PiTensorProduct
open MME.DWZComponentRestriction

universe u

set_option autoImplicit false

theorem mme_dwz_kronFin_labelled_broken_grouped_shuffle_expansion
    (K : Type u) [Field K] (m : ℕ)
    (copy : MME.DWZSquare.BrokenBlockCopy (DWZStandardBlock m))
    (g : MME.DWZTable2StandardForm.UsefulBlockShuffleGroup
      (groupedOuter (m := m))) :
    let D : DWZStandardLabelledData K m :=
      { X := TensorObj.kronFin 15
          (fun s : Fin 15 ↦ restrictedComponentPower K s m)
        basis := TensorObj.kronFinModePiBasis 15
          (fun s : Fin 15 ↦ restrictedComponentPower K s m) 2
          (fun s ↦ restrictedComponentZBasis K s m)
        label := groupedUsefulBlock m }
    let G := D.X.basisZAllowedGrading D.basis
      (fun W ↦ D.label W ∈ copy.nonholes)
    let move : Equiv.Perm (DWZStandardBlock m) := MulAction.toPerm g
    ∃ shuffleMap : ∀ i,
        (G.blockSubtensor (fun _ ↦ 0)).V i →ₗ[K] D.X.V i,
      PiTensorProduct.map shuffleMap (G.blockSubtensor (fun _ ↦ 0)).t =
        ∑ block : DWZStandardBlock m,
          if move.symm block ∈ copy.nonholes then
            dwzLabelledUsefulBlockTensor K m D block
          else 0 := by
  sorry
