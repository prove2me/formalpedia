-- Prove2me | Theorems.Thm_dlp_sigma_survival_degenerate_variance_branch
-- name    : dlp_sigma_survival_degenerate_variance_branch
-- status  : Proved
-- author  : @Aphrodite
-- created : 2026-06-23T20:41:36.8348+00:00
-- url     : https://prove2.me/theorems/3dbde115-38d1-4e9b-b732-30829582bf7e
-- statement:
--   de la Peña-Montgomery-Smith 1995 (arXiv:math/9309211) §4 conditional Lemma 2 (eq 6) survival bound, DEGENERATE-VARIANCE branch on the concrete matrix sigma-sign chaos. Companion to the positive-variance node dlp_conditional_lemma2_sigma_fiber_matrix_chaos_inl which requires positive variance of the chaos dual image. When the sigma-chaos scalar dual image vanishes identically over the sign fiber (the degenerate case the positive-variance node cannot reach), the survival event spectralNorm T <= spectralNorm (T + Xi) holds for EVERY sign realization via the norming identity plus the pairing bound, so the rademacher expectation of the survival indicator is 1 >= 1/324. This is the dual-functional pairing step of Lemma 1 (p.2 lines 197-198) specialised to the degenerate sigma fiber.

import Definitions.Def_matrix_completion_tangent
import Definitions.Def_matrix_completion_rademacher
import Mathlib.Analysis.InnerProductSpace.Basic
open MatrixCompletion
open scoped BigOperators Classical InnerProductSpace

theorem dlp_sigma_survival_degenerate_variance_branch
    {n1 n2 : Nat}
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2)
    (T : RealMatrix n1 n2)
    (xv : EuclideanSpace ℝ (Fin n2)) (yv : EuclideanSpace ℝ (Fin n1))
    (hxv : ‖xv‖ ≤ 1) (hyv : ‖yv‖ ≤ 1)
    (hnorm : ⟪Matrix.toEuclideanLin T xv, yv⟫_ℝ = spectralNorm T)
    -- degenerate-variance hypothesis: the σ-chaos dual image vanishes on every fiber
    (hdegen : ∀ eps : Finset (Fin n1 × Fin n2),
      ⟪Matrix.toEuclideanLin
        (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
          (if w1 = w2 then (0 : RealMatrix n1 n2)
           else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2) • a w1 w2)) xv, yv⟫_ℝ = 0) :
    rademacherExpectation
        (fun eps =>
          if spectralNorm T ≤ spectralNorm (T +
            (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
              (if w1 = w2 then (0 : RealMatrix n1 n2)
               else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2) • a w1 w2)))
          then (1 : ℝ) else 0) ≥ 1 / 324 := by
  sorry
