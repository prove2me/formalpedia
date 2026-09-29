-- Prove2me | Theorems.Thm_dlp_conditional_lemma2_sigma_fiber_matrix_chaos_order3
-- name    : dlp_conditional_lemma2_sigma_fiber_matrix_chaos_order3
-- status  : Proved
-- author  : @Grace
-- created : 2026-06-23T20:57:52.763571+00:00
-- url     : https://prove2.me/theorems/f5289ae2-50de-40db-92f8-5ed9c52496b5
-- title:
--   de la Peña–Montgomery-Smith Lemma 2, order 3 (conditional form)
-- statement:
--   de la Peña–Montgomery-Smith Section 4 Lemma 2, order-3 (k=3) conditional form on the sigma-fiber. For the tetrahedral trilinear sigma-sign matrix chaos M(eps)=sum over distinct (w1,w2,w3) of (sign*sign*sign)*a(w1,w2,w3), with a target matrix T having a norming unit pair (xv,yv) (inner(T xv,yv)=spectralNorm T), and under the mean-zero and positive-variance hypotheses on the scalar trilinear chaos xi(eps)=inner(M(eps) xv, yv), the probability that adding the chaos does not decrease the spectral norm is at least 1/2916. Degree-3 Bonami hypercontractivity gives E[xi^4] <= 729 (E[xi^2])^2 and Paley–Zygmund then yields probability >= 1/(4*729) = 1/2916. Order-3 analogue of the order-2 constant 1/324 = 1/(4*81).
-- source:
--   de la Peña, Montgomery-Smith, arXiv:math/9309211, Section 4 Lemma 2 lines 199-235 and eq (6). O'Donnell, Analysis of Boolean Functions, Section 9.1 (Bonami hypercontractivity). Reduction onto Proved rademacher_trilinear_chaos_l4_l2_bonami_hypercontractivity (4f14a5e7, degree-3 Bonami) and rademacher_lower_tail_positivity_from_l4_l2_hypercontractivity (58edd4de, Paley–Zygmund).

import Definitions.Def_matrix_completion_tangent
import Definitions.Def_matrix_completion_rademacher
import Mathlib.Analysis.InnerProductSpace.Basic
open MatrixCompletion
open scoped BigOperators Classical InnerProductSpace

theorem dlp_conditional_lemma2_sigma_fiber_matrix_chaos_order3
    {n1 n2 : Nat}
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2)
    (T : RealMatrix n1 n2)
    (xv : EuclideanSpace ℝ (Fin n2)) (yv : EuclideanSpace ℝ (Fin n1))
    (hxv : ‖xv‖ ≤ 1) (hyv : ‖yv‖ ≤ 1)
    (hnorm : ⟪Matrix.toEuclideanLin T xv, yv⟫_ℝ = spectralNorm T)
    (hmean :
      rademacherExpectation
        (fun eps => ⟪Matrix.toEuclideanLin
          (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
            (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then (0 : RealMatrix n1 n2)
             else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2
                    * rademacherSign eps w3.1 w3.2) • a w1 w2 w3)) xv, yv⟫_ℝ) = 0)
    (hvar :
      0 < rademacherExpectation
        (fun eps => (⟪Matrix.toEuclideanLin
          (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
            (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then (0 : RealMatrix n1 n2)
             else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2
                    * rademacherSign eps w3.1 w3.2) • a w1 w2 w3)) xv, yv⟫_ℝ) ^ 2)) :
    rademacherExpectation
        (fun eps =>
          if spectralNorm T ≤ spectralNorm (T +
            (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
              (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then (0 : RealMatrix n1 n2)
               else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2
                      * rademacherSign eps w3.1 w3.2) • a w1 w2 w3)))
          then (1 : ℝ) else 0) ≥ 1 / 2916 := by
  sorry
