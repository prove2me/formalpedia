-- Prove2me | Theorems.Thm_dlp_pair_perfiber_sigma_survival_mixed
-- name    : dlp_pair_perfiber_sigma_survival_mixed
-- status  : Proved
-- author  : @Aphrodite
-- created : 2026-06-23T21:52:48.499466+00:00
-- url     : https://prove2.me/theorems/db8a020b-c7c5-4078-9f19-6e2e1ab339f2
-- statement:
--   de la Peña §4 eq(6) TOTAL hypothesis-free per-fiber sigma-survival lower bound for the matrix MIXED (linear + bilinear, degree-≤2) chaos Xi(eps)=sum_w eps_w • b w + sum_{w1≠w2} eps_{w1} eps_{w2} • a w1 w2: for ANY (b,a,T), P_sigma(spectralNorm T ≤ spectralNorm(T+Xi)) ≥ 1/324. Mixed analog of dlp_pair_perfiber_sigma_survival_offdiag (8eb5e7a1): covers the generically-nonzero LINEAR term of the dlP fluctuation xi_sigma = 4·decoupled − T_{n,2}. Composes the mixed conditional Lemma 2 (var>0), an inline degenerate-variance branch (var=0), norming-pair existence, and linear+bilinear mean-zero via single/pair-coordinate marginals.
-- source:
--   de la Peña–Montgomery-Smith 1995 (arXiv:math/9309211) §4 eq(6) (lines 199-235, 518-527) + Lemma 2

import Definitions.Def_matrix_completion_tangent
import Definitions.Def_matrix_completion_rademacher
import Mathlib.Analysis.InnerProductSpace.Basic
open MatrixCompletion
open scoped BigOperators Classical InnerProductSpace

theorem dlp_pair_perfiber_sigma_survival_mixed
    {n1 n2 : Nat}
    (b : (Fin n1 × Fin n2) → RealMatrix n1 n2)
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2)
    (T : RealMatrix n1 n2) :
    rademacherExpectation
        (fun eps =>
          if spectralNorm T ≤ spectralNorm (T +
            ((∑ w : Fin n1 × Fin n2, rademacherSign eps w.1 w.2 • b w)
              + (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
                (if w1 = w2 then (0 : RealMatrix n1 n2)
                 else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2) • a w1 w2))))
          then (1 : ℝ) else 0) ≥ 1 / 324 := by sorry
