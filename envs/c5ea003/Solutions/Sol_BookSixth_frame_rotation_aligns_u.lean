-- Prove2me | solution 1 for BookSixth.frame_rotation_aligns_u
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-27T11:12:50.360605+00:00
-- url     : https://prove2.me/submissions/d4d83b4f-6ad7-43fe-a794-5c261672c091

import Mathlib
import Definitions.Def_BookSixth
import Definitions.Def_BookSixthRotations3
import Definitions.Def_BookSixthRotTriple

noncomputable section

open scoped BigOperators
open BookSixth Matrix

set_option maxHeartbeats 4000000

theorem solution (θ1 θ2 θ3 : ℝ) (u : Fin 3 → ℝ)
    (h1a : Real.sin θ1 * u 0 + Real.cos θ1 * u 1 = 0)
    (h2a : Real.sin θ2 * (Real.cos θ1 * u 0 - Real.sin θ1 * u 1) + Real.cos θ2 * u 2 = 0)
    (hρ2 : Real.cos θ2 * (Real.cos θ1 * u 0 - Real.sin θ1 * u 1) - Real.sin θ2 * u 2 = 1) :
    rotTriple 1 θ1 θ2 θ3 u = ![1, 0, 0] := by
  change ((rot12Matrix (1 * θ3)).mulVec (rot02Matrix (1 * θ2) *ᵥ
    (rot01Matrix (1 * θ1) *ᵥ u))) = ![1, 0, 0]
  have h1 : rot01Matrix (1 * θ1) *ᵥ u
      = ![Real.cos (1 * θ1) * u 0 - Real.sin (1 * θ1) * u 1,
        Real.sin (1 * θ1) * u 0 + Real.cos (1 * θ1) * u 1, u 2] := by
    funext i; fin_cases i
    · simp [rot01Matrix, Matrix.mulVec, Matrix.cons_val_zero, Matrix.vecHead,
        Matrix.vecTail]; ring
    · simp [rot01Matrix, Matrix.mulVec, Matrix.cons_val_one, Matrix.vecHead,
        Matrix.vecTail]
    · simp [rot01Matrix, Matrix.mulVec, Matrix.cons_val_two, Matrix.vecHead,
        Matrix.vecTail]
  have h2 : rot02Matrix (1 * θ2) *ᵥ ![Real.cos (1 * θ1) * u 0 - Real.sin (1 * θ1) * u 1,
      Real.sin (1 * θ1) * u 0 + Real.cos (1 * θ1) * u 1, u 2] = ![1, 0, 0] := by
    funext i; fin_cases i
    · simp [rot02Matrix, Matrix.mulVec, Matrix.cons_val_zero, Matrix.vecHead,
        Matrix.vecTail]; linear_combination hρ2
    · simp [rot02Matrix, Matrix.mulVec, Matrix.cons_val_one, Matrix.vecHead,
        Matrix.vecTail]; linear_combination h1a
    · simp [rot02Matrix, Matrix.mulVec, Matrix.cons_val_two, Matrix.vecHead,
        Matrix.vecTail]; linear_combination h2a
  rw [h1, h2]
  funext i; fin_cases i
  · simp [rot12Matrix, Matrix.mulVec, Matrix.cons_val_zero, Matrix.vecHead,
      Matrix.vecTail]
  · simp [rot12Matrix, Matrix.mulVec, Matrix.cons_val_one, Matrix.vecHead,
      Matrix.vecTail]
  · simp [rot12Matrix, Matrix.mulVec, Matrix.cons_val_two, Matrix.vecHead,
      Matrix.vecTail]
