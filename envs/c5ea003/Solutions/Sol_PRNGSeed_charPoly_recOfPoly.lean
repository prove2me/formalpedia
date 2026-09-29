-- Prove2me | solution 1 for PRNGSeed.charPoly_recOfPoly
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T12:35:59.9836+00:00
-- url     : https://prove2.me/submissions/1c162a02-0e30-4752-9946-4042621cec5f

import Mathlib
import Definitions.Def_MachineLearning_PRNGBerlekampMassey
import Definitions.Def_MachineLearning_PRNGSeedRecoveryLFSR
open Finset Polynomial PRNGSeed in
theorem solution {F : Type*} [CommRing F] {m : ℕ} {r : F[X]} (hr : r.Monic)
    (hd : r.natDegree = m) :
    (recOfPoly m r).charPoly = r := by
  unfold LinearRecurrence.charPoly recOfPoly
  simp only
  rw [Fin.sum_univ_eq_sum_range (fun i => (monomial i) (-r.coeff i)) m]
  -- a monic polynomial is `X^m + Σ_{i<m} c_i X^i`
  conv_rhs => rw [hr.as_sum, hd]
  simp only [map_neg, sum_neg_distrib, sub_neg_eq_add, ← X_pow_eq_monomial,
    C_mul_X_pow_eq_monomial]
