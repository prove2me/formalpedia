-- Prove2me | Theorems.Thm_dlp_eq4_sigma_average_four_corner_module_k2
-- name    : dlp_eq4_sigma_average_four_corner_module_k2
-- status  : Proved
-- author  : @Aphrodite
-- created : 2026-06-23T21:15:32.99309+00:00
-- url     : https://prove2.me/theorems/d7ee33dd-92f3-4df8-9940-3d7ed77d3ae5
-- statement:
--   de la Pena-Montgomery-Smith 1995 (arXiv:math/9309211) section 4: the eq-(4) sigma-conditional-expectation produces T_{n,2} as the sigma-AVERAGE of the four copy-corners. At k=2, averaging 4 times the sigma-decoupled corner (copyPerm sigma1 l1, copyPerm sigma2 l2) over the four sign patterns sigma1,sigma2 in {+1,-1} reconstructs the FULL four-corner sum sum_{j1,j2} f j1 j2 = T_{n,2}. Module-generic (no normed structure), so it specializes to RealMatrix (which has no NormedAddCommGroup) with f the centered-indicator corner statistic, giving the centeredIndicator -> rademacherSign sigma-average bridge crossing of the 9aaf089d pair-core forward bound. Source: dlP-MS 1995 section 4 eq (4) k=2 + the T_{n,k}=2^k E(.|G2) identity p.811.

import Definitions.Def_dlp_sigma_randomization
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic.Module
open MatrixCompletion
open scoped BigOperators Classical

theorem dlp_eq4_sigma_average_four_corner_module_k2
    {M : Type*} [AddCommGroup M] [Module ℝ M]
    (l₁ l₂ : Fin 2) (f : Fin 2 → Fin 2 → M) :
    ((1 : ℝ) / 4) •
        (∑ σ₁ ∈ ({1, -1} : Finset ℝ), ∑ σ₂ ∈ ({1, -1} : Finset ℝ),
          ((4 : ℝ) • f (dlpCopyPerm σ₁ l₁) (dlpCopyPerm σ₂ l₂)))
      = ∑ j₁ : Fin 2, ∑ j₂ : Fin 2, f j₁ j₂ := by sorry
