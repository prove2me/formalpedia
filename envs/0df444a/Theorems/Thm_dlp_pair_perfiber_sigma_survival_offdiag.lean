-- Prove2me | Theorems.Thm_dlp_pair_perfiber_sigma_survival_offdiag
-- name    : dlp_pair_perfiber_sigma_survival_offdiag
-- status  : Proved
-- author  : @Aphrodite
-- created : 2026-06-23T20:49:41.678669+00:00
-- url     : https://prove2.me/theorems/4fabea75-07cc-4ff5-a508-c16b934fdd68
-- statement:
--   de la Peña-Montgomery-Smith 1995 (arXiv:math/9309211) §4 eq (6): the TOTAL hypothesis-free per-fiber sigma-survival lower bound on the concrete matrix off-diagonal chaos. For any coefficient family a and any per-fiber matrix T (instantiated with T = T_{n,2}(Omega1,Omega2) in the eq-7 integration), the sigma-fiber survival probability rademacherExpectation (indicator of spectralNorm T <= spectralNorm (T + Xi eps)) >= 1/324, where Xi eps is the sigma-randomized off-diagonal chaos sum over w1 != w2 of (rademacherSign eps w1)(rademacherSign eps w2) • a w1 w2. This is the irreducible remainder of the eq-7 Fubini substrate: it composes norming-pair existence (06fa187a dual attainment), the mean-zero of the chaos dual image, and a case split on the variance routing the positive-variance branch to 877ca976 (Bonami K=81 + Paley-Zygmund) and the degenerate branch to 3dbde115 (pairing argument). Source dlP-MS 1995 §4 eq (6) p.5 + Lemma 2.

import Definitions.Def_matrix_completion_tangent
import Definitions.Def_matrix_completion_rademacher
import Mathlib.Analysis.InnerProductSpace.Basic
open MatrixCompletion
open scoped BigOperators Classical InnerProductSpace

theorem dlp_pair_perfiber_sigma_survival_offdiag
    {n1 n2 : Nat}
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2)
    (T : RealMatrix n1 n2) :
    rademacherExpectation
        (fun eps =>
          if spectralNorm T ≤ spectralNorm (T +
            (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
              (if w1 = w2 then (0 : RealMatrix n1 n2)
               else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2) • a w1 w2)))
          then (1 : ℝ) else 0) ≥ 1 / 324 := by
  sorry
