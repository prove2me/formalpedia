-- Prove2me | solution 1 for VectorSpaceOpt.gram_determinant_linear_independence
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-26T12:53:52.06889+00:00
-- url     : https://prove2.me/submissions/cab1e3af-f86d-4d9c-a6d2-b87629c846e5

import Mathlib
open scoped RealInnerProductSpace


theorem solution {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {n : ℕ} (y : Fin n → H) :
    (Matrix.of fun i j : Fin n => ⟪y i, y j⟫).det ≠ 0 ↔ LinearIndependent ℝ y := by
  exact Matrix.det_gram_ne_zero_iff_linearIndependent
