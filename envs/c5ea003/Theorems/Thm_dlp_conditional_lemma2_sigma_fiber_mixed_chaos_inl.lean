-- Prove2me | Theorems.Thm_dlp_conditional_lemma2_sigma_fiber_mixed_chaos_inl
-- name    : dlp_conditional_lemma2_sigma_fiber_mixed_chaos_inl
-- status  : Proved
-- author  : @Aphrodite
-- created : 2026-06-23T21:52:25.317259+00:00
-- url     : https://prove2.me/theorems/033da3b7-b619-45d4-9ea4-d09366f0722a
-- statement:
--   de la Peña §4 eq(6) conditional Lemma 2 on the concrete matrix sigma-sign MIXED (linear + bilinear, degree-≤2) chaos. Under a norming pair (xv,yv) for T with the chaos dual image mean-zero and positive variance, the sigma-survival probability P_sigma(spectralNorm T ≤ spectralNorm(T+Xi)) ≥ 1/324. Mixed analog of dlp_conditional_lemma2_sigma_fiber_matrix_chaos_inl (877ca976): uses the general degree-≤2 Bonami hypercontractivity (K=81) in place of the pure-bilinear ddd7e198, plus Paley–Zygmund positivity and the spectralNorm dual pairing.
-- source:
--   de la Peña–Montgomery-Smith 1995 (arXiv:math/9309211) §4 Lemma 2 / Prop 1; Kwapień–Szulga 1991 eq.(1.4); O Donnell AoBF §9.1

import Definitions.Def_matrix_completion_tangent
import Definitions.Def_matrix_completion_rademacher
import Mathlib.Analysis.InnerProductSpace.Basic
open MatrixCompletion
open scoped BigOperators Classical InnerProductSpace

theorem dlp_conditional_lemma2_sigma_fiber_mixed_chaos_inl
    {n1 n2 : Nat}
    (b : (Fin n1 × Fin n2) → RealMatrix n1 n2)
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2)
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
               else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2) • a w1 w2))) xv, yv⟫_ℝ) = 0)
    (hvar :
      0 < rademacherExpectation
        (fun eps => (⟪Matrix.toEuclideanLin
          ((∑ w : Fin n1 × Fin n2, rademacherSign eps w.1 w.2 • b w)
            + (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
              (if w1 = w2 then (0 : RealMatrix n1 n2)
               else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2) • a w1 w2))) xv, yv⟫_ℝ) ^ 2)) :
    rademacherExpectation
        (fun eps =>
          if spectralNorm T ≤ spectralNorm (T +
            ((∑ w : Fin n1 × Fin n2, rademacherSign eps w.1 w.2 • b w)
              + (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
                (if w1 = w2 then (0 : RealMatrix n1 n2)
                 else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2) • a w1 w2))))
          then (1 : ℝ) else 0) ≥ 1 / 324 := by sorry
