-- Prove2me | Theorems.Thm_mme_dwz_fourth_elementary_four_actual_prescribed_z_endpoints
-- name    : mme_dwz_fourth_elementary_four_actual_prescribed_z_endpoints
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-16T09:38:54.28329+00:00
-- url     : https://prove2.me/theorems/ec08ae0b-2c1f-4e6a-8dbb-e44e749d46ee
-- title:
--   Four remaining elementary raw ledger rows have actual prescribed-Z endpoints
-- statement:
--   Let $K$ be a field and use the four exact profiles from mme_dwz_fourth_elementary_four_row_data, in ledger order $10,12,18,19$, on the actual canonical $q=5$ components $T_{013},T_{301},T_{031},T_{103}$ respectively. At
--   \[\tau=\frac{790643}{1000000},\qquad R=\frac{1820522261843}{10^{12}},\]
--   each specified component, projected using its canonical Z basis and its own exact raw profile, has six-symmetrized restriction value at least $e^R$. The profile counts and denominators are unchanged from the original ledger; in particular the near-half frequencies are not rounded to one half.
-- source:
--   Duan, Wu, Zhou, Faster Matrix Multiplication via Asymmetric Hashing, https://arxiv.org/html/2210.10173v5, Definition 3.9 and Section 7.3 after Lemma 7.14, elementary boundary prescribed-Z components. The numerical specialization uses the exact published q=5 ledger profiles; the paper's entropy asymptotic is implemented as explicit arbitrarily-large finite restriction witnesses.

import Theorems.Thm_mme_dwz_q5_rectangular_four_prescribed_z_six_restriction_value
import Definitions.Def_mme_dwz_fourth_elementary_four_row_data
import Definitions.Def_mme_dwz_prescribed_z_split_value
import Theorems.Thm_mme_log_interval_of_exact_rational_series_certificate
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

open MME MME.DWZComponentRestriction MME.DWZRestrictedValue Module
open scoped BigOperators
universe u
set_option autoImplicit false

theorem mme_dwz_fourth_elementary_four_actual_prescribed_z_endpoints (K : Type u) [Field K] :
    HasPrescribedZSixRestrictionValueAtLeast
      ((cwSquareCanonicalGrading K 5).blockSubtensor (cwSquareBlockType 0 1 3))
      ((coarseClassBasis (K := K) 5 2 3).reindex Equiv.ulift.symm)
      LiftedCoarsePair.leftGrade (MME.ElementaryFourScalar.profile 0)
      (790643 / 1000000 : ℝ) (Real.exp (1820522261843 / 1000000000000 : ℝ)) ∧
    HasPrescribedZSixRestrictionValueAtLeast
      ((cwSquareCanonicalGrading K 5).blockSubtensor (cwSquareBlockType 3 0 1))
      ((coarseClassBasis (K := K) 5 2 1).reindex Equiv.ulift.symm)
      LiftedCoarsePair.leftGrade (MME.ElementaryFourScalar.profile 1)
      (790643 / 1000000 : ℝ) (Real.exp (1820522261843 / 1000000000000 : ℝ)) ∧
    HasPrescribedZSixRestrictionValueAtLeast
      ((cwSquareCanonicalGrading K 5).blockSubtensor (cwSquareBlockType 0 3 1))
      ((coarseClassBasis (K := K) 5 2 1).reindex Equiv.ulift.symm)
      LiftedCoarsePair.leftGrade (MME.ElementaryFourScalar.profile 2)
      (790643 / 1000000 : ℝ) (Real.exp (1820522261843 / 1000000000000 : ℝ)) ∧
    HasPrescribedZSixRestrictionValueAtLeast
      ((cwSquareCanonicalGrading K 5).blockSubtensor (cwSquareBlockType 1 0 3))
      ((coarseClassBasis (K := K) 5 2 3).reindex Equiv.ulift.symm)
      LiftedCoarsePair.leftGrade (MME.ElementaryFourScalar.profile 3)
      (790643 / 1000000 : ℝ) (Real.exp (1820522261843 / 1000000000000 : ℝ)) := by sorry
