-- Prove2me | solution 1 for supported_tangent_certificate_set_has_frobenius_minimizer
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-22T08:09:53.772554+00:00
-- url     : https://prove2.me/submissions/d6bb6802-1b11-4f8c-86fd-f9450a6f8dcd

import Theorems.Thm_nonempty_closed_matrix_set_has_frobenius_sq_minimizer
import Theorems.Thm_supported_tangent_certificate_set_is_closed

open MatrixCompletion

/-- Source: Candes-Recht 2008, PDF p. 17, equation (4.1).  The paper defines
the least-squares dual certificate as the minimum-Frobenius-norm element among
matrices supported on `Ω` and satisfying the tangent constraint `P_TY=E`.
This reduction separates the finite-dimensional optimization theorem from the
closedness of the supported affine constraint set. -/
theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (Omega : Finset (Fin n₁ × Fin n₂)) :
    (∃ Y : Matrix (Fin n₁) (Fin n₂) ℝ,
      VanishesOutside Omega Y ∧ tangentProjection S Y = signMatrix S) →
    ∃ Y : Matrix (Fin n₁) (Fin n₂) ℝ,
      LeastSquaresDualCertificate Omega S Y := by
  intro hNonempty
  let C : Set (Matrix (Fin n₁) (Fin n₂) ℝ) :=
    {Y | VanishesOutside Omega Y ∧ tangentProjection S Y = signMatrix S}
  have hCNonempty : C.Nonempty := by
    rcases hNonempty with ⟨Y, hY⟩
    exact ⟨Y, hY⟩
  have hCClosed : IsClosed C := by
    simpa [C] using supported_tangent_certificate_set_is_closed S Omega
  rcases nonempty_closed_matrix_set_has_frobenius_sq_minimizer C
      hCNonempty hCClosed with
    ⟨Y, hYmem, hYmin⟩
  have hYfeasible :
      VanishesOutside Omega Y ∧ tangentProjection S Y = signMatrix S := by
    simpa [C] using hYmem
  refine ⟨Y, ?_⟩
  refine ⟨hYfeasible.1, hYfeasible.2, ?_⟩
  intro Z hZsupport hZtangent
  exact hYmin Z (by simpa [C] using And.intro hZsupport hZtangent)
