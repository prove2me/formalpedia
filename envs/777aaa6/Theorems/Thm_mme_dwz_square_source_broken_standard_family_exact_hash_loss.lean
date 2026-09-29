-- Prove2me | Theorems.Thm_mme_dwz_square_source_broken_standard_family_exact_hash_loss
-- name    : mme_dwz_square_source_broken_standard_family_exact_hash_loss
-- status  : Open
-- author  : @marwahaha
-- created : 2026-08-26T18:36:43.481744+00:00
-- url     : https://prove2.me/theorems/3dff9496-c5cc-4b15-8319-ff92189f9db4
-- title:
--   Source extraction of the exact retained seven-eighths broken family
-- statement:
--   Put $L=10^{16}m$ and $g=8(4L+1)$. For every sufficiently large $m$, the literal source $(CW_6\otimes CW_6)^{\otimes L}$ restricts to a direct sum of exactly $kg$ broken standard copies. Every copy retains at least seven eighths of the literal useful-block universe. For one common modulus $p\ge2$, the number $k$ of complete repair groups satisfies
--
--   $$
--   k\ge 2^{L_{\rm ret}L}\,\frac{\lfloor p/2\rfloor}{p}\,\frac{e^{-4\sqrt{\log\lfloor p/2\rfloor}}}{D_{\rm hash}\,16(4L+1)}.
--   $$
--
--   With $p\le e^{16(L+1)}$ and $D_{\rm hash}$ equal to the explicit retained-rate polynomial denominator, this is the remaining source-and-hashing core: it includes both asymmetric hashes, all coarse-$Z$ owners, their source tensor maps and mixed-owner annihilation. It stops immediately before the already-proved flat Hole repair.
-- source:
--   Duan--Wu--Zhou, Faster Matrix Multiplication via Asymmetric Hashing, FOCS 2023 / arXiv:2210.10173v5, Additional Zeroing-Out Steps 1--4, Claim 6.8, Equation (24), and the input to Corollary 5.11, printed pp. 48--58.

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Definitions.Def_mme_dwz_square_data
import Definitions.Def_mme_dwz_table2_integer_counts
import Definitions.Def_mme_dwz_standard_labelled_z_blocks
import Definitions.Def_mme_dwz_hole_cover_data
import Definitions.Def_mme_CW_tensor

open MME BigOperators Filter
open MME.DWZSquare MME.DWZComponentRestriction

universe u

set_option autoImplicit false

theorem mme_dwz_square_source_broken_standard_family_exact_hash_loss
    {K : Type u} [Field K] :
    ∀ᶠ m : ℕ in atTop,
      let L : ℕ := MME.DWZTable2Counts.scale * m
      let g : ℕ := 8 * (4 * L + 1)
      let x : ℝ := (((L + 1 : ℕ) : ℝ))
      let jointPoly : ℝ := (6 * x) ^ 15
      let degreePoly : ℝ := (6 * x) ^ 5 * x ^ 15
      let zPoly : ℝ := (6 * x) ^ 5
      let compatibilityPoly : ℝ := (6 * x) ^ 9
      let Dhash : ℝ :=
        32 * max (jointPoly * degreePoly) (zPoly * compatibilityPoly)
      ∃ (k p : ℕ)
          (copies : Fin (k * g) → BrokenBlockCopy (DWZStandardBlock m)),
        0 < m ∧
        2 ≤ p ∧
        (p : ℝ) ≤ Real.exp (16 * (((L + 1 : ℕ) : ℝ))) ∧
        (∀ r,
          7 * Fintype.card (DWZStandardBlock m) ≤
            8 * (copies r).nonholes.card) ∧
        (let D : DWZStandardLabelledData K m :=
            { X := TensorObj.kronFin 15
                (fun r : Fin 15 ↦ restrictedComponentPower K r m)
              basis := TensorObj.kronFinModePiBasis 15
                (fun r : Fin 15 ↦ restrictedComponentPower K r m) 2
                (fun r ↦ restrictedComponentZBasis K r m)
              label := groupedUsefulBlock m }
          let G : Fin (k * g) → D.X.TypeGrading 2 := fun r ↦
            D.X.basisZAllowedGrading D.basis
              (fun W ↦ D.label W ∈ (copies r).nonholes)
          TensorObj.Restrict
            (TensorObj.bigAdd (fun r ↦
              (G r).blockSubtensor (fun _ ↦ 0)))
            ((TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow L)) ∧
        Real.rpow 2 (retainedLogRate * (L : ℝ)) *
            (((((p / 2 : ℕ) : ℝ) / (p : ℝ)) *
                Real.exp
                  (-4 * Real.sqrt
                    (Real.log (((p / 2 : ℕ) : ℝ))))) /
              (Dhash * (16 * (((4 * L + 1 : ℕ) : ℝ))))) ≤
          (k : ℝ) := by
  sorry
