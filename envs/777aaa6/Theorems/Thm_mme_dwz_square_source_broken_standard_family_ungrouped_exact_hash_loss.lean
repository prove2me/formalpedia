-- Prove2me | Theorems.Thm_mme_dwz_square_source_broken_standard_family_ungrouped_exact_hash_loss
-- name    : mme_dwz_square_source_broken_standard_family_ungrouped_exact_hash_loss
-- status  : Open
-- author  : @marwahaha
-- created : 2026-08-26T19:20:46.919219+00:00
-- url     : https://prove2.me/theorems/207db882-3f67-4cb2-881f-fc6416340a22
-- title:
--   DWZ Equation (24): ungrouped broken-owner family with exact hash loss
-- statement:
--   For every field and all sufficiently large positive Table-2 scales, the powered q=6 Coppersmith--Winograd square restricts to a finite direct sum of $n$ literal broken standard copies. Every copy retains at least seven eighths of its standard blocks. A common prime $p$ satisfies the explicit exponential upper bound, and $n$ is at least the full Equation-(24) retained-copy term: the base-two retained rate times the exact prime-floor and Behrend factor, divided by the explicit hash polynomial denominator. This lower bound is also eventually at least twice the fixed repair-group size $g=8(4L+1)$. The family is deliberately ungrouped: no divisibility of $n$ by $g$ is assumed. The theorem isolates the actual all-owner source restriction, mixed-owner annihilation, common-prime hashing, and cardinality construction before the generic incomplete-group deletion and Hole repair steps.
-- source:
--   Duan--Wu--Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Claim 6.8, Corollary 5.11, Equation (24), and the q=6/Table-2 specialization in Section 6.3, printed pp. 48--59; https://arxiv.org/abs/2210.10173

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

theorem mme_dwz_square_source_broken_standard_family_ungrouped_exact_hash_loss
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
      ∃ (n p : ℕ)
          (copies : Fin n → BrokenBlockCopy (DWZStandardBlock m)),
        let A : ℝ :=
          Real.rpow 2 (retainedLogRate * (L : ℝ)) *
            (((((p / 2 : ℕ) : ℝ) / (p : ℝ)) *
                Real.exp
                  (-4 * Real.sqrt
                    (Real.log (((p / 2 : ℕ) : ℝ))))) /
              Dhash)
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
          let G : Fin n → D.X.TypeGrading 2 := fun r ↦
            D.X.basisZAllowedGrading D.basis
              (fun W ↦ D.label W ∈ (copies r).nonholes)
          TensorObj.Restrict
            (TensorObj.bigAdd (fun r ↦
              (G r).blockSubtensor (fun _ ↦ 0)))
            ((TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow L)) ∧
        2 * (g : ℝ) ≤ A ∧
        A ≤ (n : ℝ) := by
  sorry
