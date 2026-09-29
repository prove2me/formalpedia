-- Prove2me | Theorems.Thm_mme_dwz_square_source_aligned_broken_family_ungrouped_aggregate_hash_mass
-- name    : mme_dwz_square_source_aligned_broken_family_ungrouped_aggregate_hash_mass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T19:06:00.235865+00:00
-- url     : https://prove2.me/theorems/47d4a496-e5ad-46e9-875e-119503b5e8f6
-- title:
--   DWZ global asymmetric hash retains the source aggregate non-hole mass
-- statement:
--   For all sufficiently large Table-2 scales $m$, let $L$ be the scaled tensor-power length and let $D_{\mathrm{hash}}$ be the same explicit polynomial denominator used in the square $\omega<2.3747$ analysis. There is one prime modulus $p$, one globally retained exact-profile family of source outer words, and one literal Claim-6.8 broken copy for every retained owner such that:
--
--   1. every outer word has the exact fifteen-component Table-2 histogram;
--   2. the direct sum of all source-aligned broken objects is a restriction of $(\mathrm{CW}_6\otimes\mathrm{CW}_6)^{\otimes L}$; and
--   3. their normalized non-hole fractions satisfy
--
--   $$
--   2^{\rho L}\,\frac{(\lfloor p/2\rfloor/p)e^{-4\sqrt{\log\lfloor p/2\rfloor}}}{D_{\mathrm{hash}}}
--   +\;\le\;\sum_r \eta_r.
--   $$
--
--   Here $\rho$ is the retained Table-2 logarithmic rate. The result records the aggregate quantifier used by the DWZ probabilistic argument and Hole Lemma. It deliberately does not strengthen that argument to one common hash state for which every owner separately has non-hole fraction at least $7/8$.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5 / FOCS 2023, Section 6, especially Equation (21), Claim 6.8, and the aggregate use of Lemma 5.6 (printed pp. 54-58 / PDF pp. 55-59).

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Definitions.Def_mme_dwz_square_data
import Definitions.Def_mme_dwz_table2_integer_counts
import Definitions.Def_mme_dwz_standard_labelled_z_blocks
import Definitions.Def_mme_dwz_hole_cover_data
import Definitions.Def_mme_dwz_source_aligned_broken_obj
import Definitions.Def_mme_CW_tensor

open MME BigOperators Filter
open MME.DWZSquare MME.DWZComponentRestriction

universe u

set_option autoImplicit false

/-- Paper-faithful replacement for the overstrong pointwise-seven-eighths
source leaf.  One common affine state retains the required *aggregate*
non-hole mass, which is exactly the input consumed by the Hole Lemma. -/

theorem mme_dwz_square_source_aligned_broken_family_ungrouped_aggregate_hash_mass
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
          (outer : Fin n → Fin L → Fin 15)
          (copies : ∀ r : Fin n, BrokenBlockCopy
            (MME.DWZTable2StandardForm.UsefulBlock m (outer r))),
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
        (∀ r s,
          Fintype.card {t : Fin L // outer r t = s} =
            MME.DWZTable2Counts.component s * m) ∧
        TensorObj.Restrict
          (TensorObj.bigAdd (fun r ↦
            MME.DWZSourceAligned.brokenAddressObj K m
              (outer r) (copies r)))
          ((TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow L) ∧
        A ≤ ∑ r, nonholeFraction (copies r) := by
  sorry
