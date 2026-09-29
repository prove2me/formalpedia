-- Prove2me | Theorems.Thm_mme_dwz_broken_standard_owner_projection_realizes_exact_sum
-- name    : mme_dwz_broken_standard_owner_projection_realizes_exact_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T10:34:43.986011+00:00
-- url     : https://prove2.me/theorems/f3511e3c-b2d6-409c-b824-988cfb48def2
-- title:
--   A broken Table-2 copy maps to its exact owner-assigned block sum
-- statement:
--   Let a literal broken Table-2 standard copy be mapped by a supplied shuffle realization to the sum of exactly those useful-block tensors whose inverse-moved labels are nonholes. Fix an owner assignment and one copy index t, and assume every block owned by t is a nonhole in this copy. Then there are modewise maps from the broken copy into the standard object such that: (1) their X and Y maps are exactly the supplied shuffle maps, and (2) their tensor image is the exact sum of the standard useful-block tensors owned by t: $$F_t(T_{\mathrm{broken}})=\sum_b \mathbf{1}_{t=\operatorname{owner}(b)}\,T_b.$$ The construction changes only Z, by the owner-selecting diagonal projection. The conclusion is an equality of tensors and is the direct per-copy input to exact-once Hole-Lemma repair.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5 / FOCS 2023, Section 5 Hole Lemma repair (especially the standard-form shuffling/zeroing step), Definition 5.4, and Definition 6.3 (PDF pp.47 and 53 / printed pp.46 and 52).

import Definitions.Def_mme_dwz_standard_labelled_z_blocks
import Theorems.Thm_mme_dwz_owner_projection_standard_useful_block_tensor

open BigOperators Finset
open MME Module PiTensorProduct
open MME.DWZComponentRestriction

universe u

set_option autoImplicit false

theorem mme_dwz_broken_standard_owner_projection_realizes_exact_sum
    (K : Type u) [Field K] (m : ℕ) {s : ℕ}
    (copy : MME.DWZSquare.BrokenBlockCopy (DWZStandardBlock m))
    (move : Equiv.Perm (DWZStandardBlock m))
    (owner : DWZStandardBlock m → Fin s) (t : Fin s)
    (shuffleMap : ∀ i,
      (dwzBrokenStandardObj K m copy).V i →ₗ[K]
        (dwzStandardLabelledData K m).X.V i)
    (hshuffle :
      PiTensorProduct.map shuffleMap (dwzBrokenStandardObj K m copy).t =
        ∑ block : DWZStandardBlock m,
          if move.symm block ∈ copy.nonholes then
            dwzStandardUsefulBlockTensor K m block
          else 0)
    (howner : ∀ block : DWZStandardBlock m, t = owner block →
      move.symm block ∈ copy.nonholes) :
    ∃ f : ∀ i,
        (dwzBrokenStandardObj K m copy).V i →ₗ[K]
          (dwzStandardLabelledData K m).X.V i,
      f 0 = shuffleMap 0 ∧
      f 1 = shuffleMap 1 ∧
      PiTensorProduct.map f (dwzBrokenStandardObj K m copy).t =
        ∑ block : DWZStandardBlock m,
          if t = owner block then
            dwzStandardUsefulBlockTensor K m block
          else 0 := by
  sorry
