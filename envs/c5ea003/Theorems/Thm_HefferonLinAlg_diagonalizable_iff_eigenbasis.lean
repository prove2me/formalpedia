-- Prove2me | Theorems.Thm_HefferonLinAlg_diagonalizable_iff_eigenbasis
-- name    : HefferonLinAlg.diagonalizable_iff_eigenbasis
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-08-07T03:56:56.421575+00:00
-- url     : https://prove2.me/theorems/a226b5d9-82eb-41c7-b528-5612caf49685
-- title:
--   Diagonalizable exactly when there is an eigenbasis
-- statement:
--   An $n \times n$ matrix $A$ over a field $K$ is similar to a diagonal matrix if and only if $K^n$ has a basis of eigenvectors of $A$ — a basis $B$ together with scalars $\lambda_i$ satisfying $A B_i = \lambda_i B_i$ for every $i$. This is the first canonical form of Chapter Five and the model for the last one: Jordan form is what one settles for when no eigenbasis exists.
-- source:
--   Jim Hefferon, *Linear Algebra*, Saint Michael's College, 2020 printing, Chapter Five, Section II.2, Lemma 2.4, printed p. 409 (PDF p. 419)

import Mathlib

open Matrix

namespace HefferonLinAlg

theorem diagonalizable_iff_eigenbasis
    {K : Type*} [Field K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K) :
    (∃ (P : Matrix (Fin n) (Fin n) K) (d : Fin n → K),
        IsUnit P.det ∧ P⁻¹ * A * P = Matrix.diagonal d) ↔
      (∃ (B : Module.Basis (Fin n) K (Fin n → K)) (lam : Fin n → K),
        ∀ i, A *ᵥ B i = lam i • B i) := by
  sorry

end HefferonLinAlg
