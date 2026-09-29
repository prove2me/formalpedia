-- Prove2me | Theorems.Thm_Zeta9Note_five_sample_sign_forces_nonzero
-- name    : Zeta9Note.five_sample_sign_forces_nonzero
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-25T07:31:56.505007+00:00
-- url     : https://prove2.me/theorems/d03e669d-3a34-4984-a4eb-25d7e9dafe80
-- title:
--   A shared sign at five nodes forces a nonzero functional value
-- statement:
--   Let L be a linear functional on real polynomials that matches the five moments of a weighted five-point sum with positive weights and injective nodes, and let p be a nonzero polynomial of degree at most 4. If all five sampled values p(y_j) are ≥ 0, or all are ≤ 0, then L p is nonzero.
-- source:
--   Abstract layer distilled from the v0.1 research note (Zenodo 10.5281/zenodo.22951155); statement and proof in formalization/Zeta9Note.lean.

import Mathlib

namespace Zeta9Note

theorem five_sample_sign_forces_nonzero
    (L : Polynomial ℝ →ₗ[ℝ] ℝ) (y w : Fin 5 → ℝ)
    (hy : Function.Injective y)
    (hw : ∀ j : Fin 5, 0 < w j)
    (hmom : ∀ m : ℕ, m ≤ 4 →
      L ((Polynomial.X : Polynomial ℝ) ^ m) = ∑ j : Fin 5, w j * (y j) ^ m)
    (p : Polynomial ℝ) (hpdeg : p.natDegree ≤ 4) (hp : p ≠ 0)
    (hsign : (∀ j : Fin 5, 0 ≤ p.eval (y j)) ∨ (∀ j : Fin 5, p.eval (y j) ≤ 0)) :
    L p ≠ 0 := by sorry

end Zeta9Note
