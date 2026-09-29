-- Prove2me | Theorems.Thm_dlp_conditional_lemma2_sigma_fiber_mixed3_chaos_inl
-- name    : dlp_conditional_lemma2_sigma_fiber_mixed3_chaos_inl
-- status  : Proved
-- author  : @Aphrodite
-- created : 2026-06-24T02:57:26.827578+00:00
-- url     : https://prove2.me/theorems/27376bda-6d79-4e8c-8baf-3420c53ed3e2
-- statement:
--   Order-3 conditional Lemma 2 of de la Pena-Montgomery-Smith on the concrete matrix sigma-sign MIXED (linear + bilinear + trilinear, degree-<=3) chaos. Given a fixed matrix T with a norming unit pair (xv,yv) (so <T xv, yv> = spectralNorm T), and given that the dual-image scalar chaos F(eps) = <Xi(eps) xv, yv> is mean-zero with positive variance, the sigma-survival probability P_sigma(spectralNorm T <= spectralNorm (T + Xi)) >= 1/2916, where Xi(eps) = sum_w sgn_w . b_w + sum_{w1!=w2} sgn.sgn . a + sum_{distinct} sgn.sgn.sgn . cc. Reduction onto the degree-<=3 mixed Bonami hypercontractivity (K=729), the Rademacher Paley-Zygmund lower-tail positivity (giving 1/(4*729)=1/2916), and spectral-norm dual attainment / inner-pairing containment. Order-3 analog of dlp_conditional_lemma2_sigma_fiber_mixed_chaos_inl (033da3b7). Source: dlP-MS 1995 (arXiv:math/9309211) sec 4 Lemma 2/Prop 1 + Kwapien-Szulga 1991 eq 1.4.

import Definitions.Def_matrix_completion_tangent
import Definitions.Def_matrix_completion_rademacher
import Mathlib.Analysis.InnerProductSpace.Basic
open MatrixCompletion
open scoped BigOperators Classical InnerProductSpace

theorem dlp_conditional_lemma2_sigma_fiber_mixed3_chaos_inl
    {n1 n2 : Nat}
    (b : (Fin n1 × Fin n2) → RealMatrix n1 n2)
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2)
    (cc : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2)
    (T : RealMatrix n1 n2)
    (xv : EuclideanSpace ℝ (Fin n2)) (yv : EuclideanSpace ℝ (Fin n1))
    (hxv : ‖xv‖ ≤ 1) (hyv : ‖yv‖ ≤ 1)
    (hnorm : ⟪Matrix.toEuclideanLin T xv, yv⟫_ℝ = spectralNorm T)
    (hmean :
      rademacherExpectation
        (fun eps => ⟪Matrix.toEuclideanLin
          ((∑ w : Fin n1 × Fin n2, rademacherSign eps w.1 w.2 • b w)
            + (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
              (if w1 = w2 then (0 : RealMatrix n1 n2)
               else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2) • a w1 w2))
            + (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
              (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then (0 : RealMatrix n1 n2)
               else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2
                      * rademacherSign eps w3.1 w3.2) • cc w1 w2 w3))) xv, yv⟫_ℝ) = 0)
    (hvar :
      0 < rademacherExpectation
        (fun eps => (⟪Matrix.toEuclideanLin
          ((∑ w : Fin n1 × Fin n2, rademacherSign eps w.1 w.2 • b w)
            + (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
              (if w1 = w2 then (0 : RealMatrix n1 n2)
               else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2) • a w1 w2))
            + (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
              (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then (0 : RealMatrix n1 n2)
               else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2
                      * rademacherSign eps w3.1 w3.2) • cc w1 w2 w3))) xv, yv⟫_ℝ) ^ 2)) :
    rademacherExpectation
        (fun eps =>
          if spectralNorm T ≤ spectralNorm (T +
            ((∑ w : Fin n1 × Fin n2, rademacherSign eps w.1 w.2 • b w)
              + (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
                (if w1 = w2 then (0 : RealMatrix n1 n2)
                 else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2) • a w1 w2))
              + (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
                (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then (0 : RealMatrix n1 n2)
                 else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2
                        * rademacherSign eps w3.1 w3.2) • cc w1 w2 w3))))
          then (1 : ℝ) else 0) ≥ 1 / 2916 := by
  sorry
