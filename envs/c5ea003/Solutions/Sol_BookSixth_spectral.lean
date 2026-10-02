-- Prove2me | solution 1 for BookSixth.spectral
-- status  : ACCEPTED   (prove)
-- author  : @xiangyazi24
-- created : 2026-09-13T01:38:03.335444+00:00
-- url     : https://prove2.me/submissions/c28e8577-cea4-4f96-b5de-a66a4d814cc4

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) :
    ∃ Q : Matrix.unitaryGroup (Fin n) ℝ, ∃ d : Fin n → ℝ,
      star (Q : Matrix (Fin n) (Fin n) ℝ) * A * Q = Matrix.diagonal d := by
  refine ⟨hA.eigenvectorUnitary, hA.eigenvalues, ?_⟩
  simpa [Unitary.conjStarAlgAut_star_apply] using hA.conjStarAlgAut_star_eigenvectorUnitary

