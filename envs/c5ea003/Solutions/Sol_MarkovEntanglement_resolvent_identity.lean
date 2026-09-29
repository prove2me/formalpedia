-- Prove2me | solution 1 for MarkovEntanglement.resolvent_identity
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-07T15:26:31.640604+00:00
-- url     : https://prove2.me/submissions/27942d60-9434-4b65-9a3e-620823169b07

import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.Abel

/-!
Chen and Peng, *Multi-agent Markov Entanglement*, arXiv:2506.02385v3, Lemma 1, p. 17
(quoted there from Farias, Gupta and Ruan (2023), Lemma 1).

With `A = 1 - P'` and `B = 1 - P` this is exactly the resolvent expansion
`A⁻¹ - B⁻¹ = A⁻¹ (B - A) B⁻¹`, available in Mathlib as `Matrix.inv_sub_inv`, once one
notes `B - A = (1 - P) - (1 - P') = P' - P`.  The determinant hypotheses give
invertibility of both matrices, so the `IsUnit A ↔ IsUnit B` side condition is
the trivially true iff.
-/

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P P' : Matrix ι ι ℝ) (hP : IsUnit (1 - P).det) (hP' : IsUnit (1 - P').det) :
    (1 - P')⁻¹ - (1 - P)⁻¹ = (1 - P')⁻¹ * (P' - P) * (1 - P)⁻¹ := by
  have hA : IsUnit (1 - P') := (Matrix.isUnit_iff_isUnit_det _).2 hP'
  have hB : IsUnit (1 - P) := (Matrix.isUnit_iff_isUnit_det _).2 hP
  have hsub : P' - P = (1 - P) - (1 - P') := by abel
  rw [hsub, Matrix.inv_sub_inv (iff_of_true hA hB)]
