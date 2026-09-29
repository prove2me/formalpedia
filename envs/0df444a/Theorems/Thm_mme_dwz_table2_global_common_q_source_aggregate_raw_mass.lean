-- Prove2me | Theorems.Thm_mme_dwz_table2_global_common_q_source_aggregate_raw_mass
-- name    : mme_dwz_table2_global_common_q_source_aggregate_raw_mass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T19:51:10.098587+00:00
-- url     : https://prove2.me/theorems/8257e89d-6db8-47e0-ab05-6dbf4c4fbbad
-- title:
--   Global common-state DWZ source family with aggregate nonhole mass
-- statement:
--   At every sufficiently large Table-2 scale, one can retain an exact joint-profile family inside a single canonical first-hash bucket and choose one common affine state for its second hash. The associated literal source-aligned broken tensors are a restriction of the square Coppersmith--Winograd power, and their normalized nonhole fractions satisfy
--
--   $$
--   \frac{|T|\,|S|}{2p^2}\leq\sum_r\eta_r.
--   $$
--
--   The same witnesses satisfy the standard two-branch degree, prime, entropy, and Behrend estimates. This is the aggregate form of the DWZ Claim 6.8 source construction; no pointwise seven-eighths assertion is made.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 6, especially Definition 6.3, Claim 6.8, and Additional Zeroing-Out Step 2; https://arxiv.org/abs/2210.10173

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Definitions.Def_mme_dwz_square_data
import Definitions.Def_mme_dwz_table2_integer_counts
import Definitions.Def_mme_dwz_hole_cover_data
import Definitions.Def_mme_dwz_source_aligned_broken_obj
import Definitions.Def_mme_dwz_global_common_state_broken_copy
import Definitions.Def_mme_CW_tensor

open MME BigOperators Filter
open MME.DWZSquare MME.DWZComponentRestriction

universe u

set_option autoImplicit false

/-- The remaining paper-facing source/hash construction.  It selects one
common affine state for the full exact-profile family and controls the sum of
nonhole fractions; it deliberately makes no pointwise seven-eighths claim. -/

theorem mme_dwz_table2_global_common_q_source_aggregate_raw_mass
    {K : Type u} [Field K] :
    ∀ᶠ m : ℕ in atTop,
      let L : ℕ := MME.DWZTable2Counts.scale * m
      ∃ (n p N fixedTargetCard d Q : ℕ)
          (R : ℝ) (S : Finset ℕ)
          (reindex : Fin (N + 1) ≃ Fin L)
          (q : (Fin (N + 2) → ZMod p) × ZMod p)
          (edge : Fin n → Fin (N + 1) → Fin 15),
        0 < m ∧
        2 ≤ p ∧
        Nat.multinomial Finset.univ
              (fun s : Fin 15 ↦ MME.DWZTable2Counts.component s * m) =
            Nat.multinomial Finset.univ
                (fun k : Fin 5 ↦ MME.DWZTable2Counts.alphaZ k * m) *
              fixedTargetCard ∧
        0 < d ∧
        (d : ℝ) ≤
          (6 * (((L + 1 : ℕ) : ℝ))) ^ 5 *
            (((L + 1 : ℕ) : ℝ)) ^ 15 *
            Real.exp
              ((m : ℝ) * (MME.DWZTable2Counts.scale : ℝ) * Real.log 2 *
                (MME.DWZSquare.maxSameMarginalEntropy -
                  mme_modern_entropyBits
                    (mme_modern_marginal MME.DWZSquare.shapeX
                      MME.DWZSquare.alpha))) ∧
        R =
          (6 * (((L + 1 : ℕ) : ℝ))) ^ 9 *
            (fixedTargetCard : ℝ) *
            Real.exp
              ((m : ℝ) * (MME.DWZTable2Counts.scale : ℝ) * Real.log 2 *
                MME.DWZSquare.logAlphaP) ∧
        (p : ℝ) ≤ max 8 (16 * max (d : ℝ) R) ∧
        d ≤ 15 ^ L ∧
        Q ≤ 15 ^ L ∧
        p ≤ 2 * max 4 (8 * max d Q) ∧
        ((p / 2 : ℕ) : ℝ) *
              Real.exp (-4 * Real.sqrt
                (Real.log (((p / 2 : ℕ) : ℝ)))) ≤
            (S.card : ℝ) ∧
        (∀ r s,
          Fintype.card
              {t : Fin L //
                MME.DWZGlobalCorrelated.sourceWord reindex edge r t = s} =
            MME.DWZTable2Counts.component s * m) ∧
        TensorObj.Restrict
          (TensorObj.bigAdd (fun r ↦
            MME.DWZSourceAligned.brokenAddressObj K m
              (MME.DWZGlobalCorrelated.sourceWord reindex edge r)
              (MME.DWZGlobalCorrelated.commonStateBrokenCopy
                m reindex q edge r)))
          ((TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow L) ∧
        ((Nat.multinomial Finset.univ
              (fun s : Fin 15 ↦ MME.DWZTable2Counts.component s * m) : ℝ) *
            (S.card : ℝ)) /
            (2 * (p : ℝ) ^ 2) ≤
          ∑ r, MME.DWZSquare.nonholeFraction
            (MME.DWZGlobalCorrelated.commonStateBrokenCopy
              m reindex q edge r) := by
  sorry
