-- Prove2me | Theorems.Thm_mme_dwz_square_source_broken_standard_family_ungrouped_hash_count
-- name    : mme_dwz_square_source_broken_standard_family_ungrouped_hash_count
-- status  : Open
-- author  : @marwahaha
-- created : 2026-08-26T20:10:16.593781+00:00
-- url     : https://prove2.me/theorems/489c96c0-193d-4518-81fe-c13935d53c0a
-- title:
--   Source hashing produces the full ungrouped broken-standard family at the exact retained count
-- statement:
--   For every field $K$ and every sufficiently large Table-2 scale parameter $m$, put $L=10^{16}m$. The source-faithful asymmetric-hashing construction produces a common prime $p$ and an ungrouped family of $n$ literal broken copies of the standard fifteen-component Table-2 object. Every copy retains at least seven eighths of its labelled blocks, and the direct sum of all $n$ masked copies is a restriction of $(CW_6\otimes CW_6)^{\otimes L}$.
--
--   With the exact polynomial denominator $D_{\rm hash}$ displayed in the formal statement, the number of produced owners satisfies
--
--   $$
--   2^{\rho L}\,\frac{\lfloor p/2\rfloor}{p}\,\frac{\exp(-4\sqrt{\log\lfloor p/2\rfloor})}{D_{\rm hash}}\le n.
--   $$
--
--   The theorem deliberately stops before grouping the copies for the Hole Lemma. It records the all-owner source restriction and exact retained count; the eventual inequality ensuring enough complete groups is a separate analytic theorem.
-- source:
--   Duan--Wu--Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Claim 6.8, Corollary 5.11, and the finite retained-copy count leading to Equation (24), printed pp. 48 and 54--58; https://arxiv.org/abs/2210.10173

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

theorem mme_dwz_square_source_broken_standard_family_ungrouped_hash_count
    {K : Type u} [Field K] :
    ∀ᶠ m : ℕ in atTop,
      let L : ℕ := MME.DWZTable2Counts.scale * m
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
        A ≤ (n : ℝ) := by
  sorry
