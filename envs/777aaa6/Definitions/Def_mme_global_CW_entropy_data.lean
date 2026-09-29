-- Prove2me | Definitions.Def_mme_global_CW_entropy_data
-- name    : mme_global_CW_entropy_data
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-09-22T08:46:56.223803+00:00
-- url     : https://prove2.me/theorems/3bf3f844-e941-4c12-b717-08ce4914bd9e
-- title:
--   Unpaired global entropy rate and explicit finite losses
-- statement:
--   Defines the pooled global X/Y/Z entropy rate from exact coarse-word histograms and explicit polynomial, hash and repair losses. There is no paired-parent concentration loss.
-- source:
--   Finite global entropy and tolerance estimates for More Asymmetry Theorem 5.3.

import Definitions.Def_mme_global_CW_counted_stage
import Definitions.Def_mme_regional_entropy_copy_bound
open BigOperators MME MME.RecursiveYZ MME.RegionRate
open scoped Classical
set_option autoImplicit false
namespace MME.GlobalCW

/-- Conditional word entropy summed over the exact global coarse histogram. -/
noncomputable def CountedStage.wordPotential {ell M : ℕ} (D : CountedStage ell M)
    (i : Fin 3) : ℝ :=
  ∑ g : Fin D.R × Fin (D.degree+1),
    massEntropy (fun w ↦ (aggregate i (D.mu i) g.1 g.2 w : ℝ))

/-- The three global rates are summed over regions before taking their minimum. -/
noncomputable def CountedStage.entropyRate {ell M : ℕ} (D : CountedStage ell M) : ℝ :=
  min (coarsePotential D.m 0 - penaltyPotential D.n D.m)
    (min (coarsePotential D.m 1 + D.wordPotential 1 - compatibilityPotential 0 (D.mu 1))
      (coarsePotential D.m 2 + D.wordPotential 2 - compatibilityPotential 1 (D.mu 2)))

noncomputable def CountedStage.entropyExponent {ell M : ℕ} (D : CountedStage ell M) : ℝ :=
  jointPotential D.m - D.entropyRate

noncomputable def CountedStage.entropyLoadFactor {ell M : ℕ} (D : CountedStage ell M) : ℝ :=
  8 * ambientFactor (half := D.degree) (parent := D.bounds) D.n *
      polynomialFactor D.n (D.R * (D.degree+1)) +
    128 * (D.repairScale : ℝ) * polynomialFactor D.n (D.R * (D.degree+1)) *
      polynomialFactor D.n (D.R * (D.degree+1) * Fintype.card (CompleteSplit.CompleteWord ell))

noncomputable def CountedStage.entropyScaleFactor {ell M : ℕ} (D : CountedStage ell M) : ℝ :=
  (D.degree : ℝ) + 2 + D.entropyLoadFactor

/-- A finite lower bound for the certified log copy count, including every
polynomial, progression-free-set, and repair loss. -/
noncomputable def CountedStage.entropyLogCopies {ell M : ℕ} (D : CountedStage ell M) : ℝ :=
  D.entropyRate - Real.log (polynomialFactor D.n (Fintype.card (Cell D.degree D.R D.bounds))) -
    Real.log (64 * D.entropyScaleFactor) -
    4 * Real.sqrt (Real.log D.entropyScaleFactor + D.entropyExponent) -
    D.repairExponent * Real.log 8
end MME.GlobalCW


