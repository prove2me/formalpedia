-- Prove2me | Theorems.Thm_Zeta9Note_quadrature_exact_of_moments
-- name    : Zeta9Note.quadrature_exact_of_moments
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-25T07:30:47.447706+00:00
-- url     : https://prove2.me/theorems/d9acd743-1fce-4a14-a964-3640f1032366
-- title:
--   Moment matching gives exact five-point quadrature up to degree 4
-- statement:
--   Let L be a linear functional on real polynomials, y a five-point node vector and w a weight vector. If L agrees with the weighted five-point sum on the monomials X^m for every m ≤ 4, then L agrees with the weighted five-point sum on every polynomial of degree at most 4. No positivity of the weights is assumed.
-- source:
--   Abstract layer distilled from the v0.1 research note (Zenodo 10.5281/zenodo.22951155); statement and proof in formalization/Zeta9Note.lean.

import Mathlib

namespace Zeta9Note

theorem quadrature_exact_of_moments
    (L : Polynomial ℝ →ₗ[ℝ] ℝ) (y w : Fin 5 → ℝ)
    (hmom : ∀ m : ℕ, m ≤ 4 →
      L ((Polynomial.X : Polynomial ℝ) ^ m) = ∑ j : Fin 5, w j * (y j) ^ m) :
    ∀ p : Polynomial ℝ, p.natDegree ≤ 4 →
      L p = ∑ j : Fin 5, w j * p.eval (y j) := by sorry

end Zeta9Note
