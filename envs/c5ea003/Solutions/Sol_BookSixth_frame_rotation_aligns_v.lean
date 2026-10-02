-- Prove2me | solution 1 for BookSixth.frame_rotation_aligns_v
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-27T11:13:09.915755+00:00
-- url     : https://prove2.me/submissions/14fead3f-0bf5-45a2-acfe-1b0736854628

import Mathlib
import Definitions.Def_BookSixth
import Definitions.Def_BookSixthRotations3
import Definitions.Def_BookSixthRotTriple
import Theorems.Thm_BookSixth_threefold_rotation_preserves_inner_product

noncomputable section

open scoped BigOperators
open BookSixth Matrix

set_option maxHeartbeats 4000000

private lemma third_zero (w : Fin 3 → ℝ) (hn : (∑ i, w i * w i) = 1)
    (h0 : w 0 = 0) (h1 : w 1 = 1) : w 2 = 0 := by
  have h2 := hn
  simp only [Fin.sum_univ_succ] at h2
  norm_num [Fin.isValue, h0, h1] at h2
  nlinarith [sq_nonneg (w 2)]

/-- The three rotations carry the second frame vector onto the 2-axis. The third
coordinate is forced by squared-norm preservation, so the published `h3a` — which
mixes `u` into the `v` terms — is never needed. -/
theorem solution (θ1 θ2 θ3 : ℝ) (v : Fin 3 → ℝ) (hv : (∑ i, v i * v i) = 1)
    (hρ3 : Real.cos θ3 * (Real.sin θ1 * v 0 + Real.cos θ1 * v 1)
      - Real.sin θ3 * (Real.sin θ2 * (Real.cos θ1 * v 0 - Real.sin θ1 * v 1)
        + Real.cos θ2 * v 2) = 1)
    (hd0 : Real.cos θ2 * (Real.cos θ1 * v 0 - Real.sin θ1 * v 1)
      - Real.sin θ2 * v 2 = 0) :
    rotTriple 1 θ1 θ2 θ3 v = ![0, 1, 0] := by
  change ((rot12Matrix (1 * θ3)).mulVec (rot02Matrix (1 * θ2) *ᵥ
    (rot01Matrix (1 * θ1) *ᵥ v))) = ![0, 1, 0]
  have h1 : rot01Matrix (1 * θ1) *ᵥ v
      = ![Real.cos (1 * θ1) * v 0 - Real.sin (1 * θ1) * v 1,
        Real.sin (1 * θ1) * v 0 + Real.cos (1 * θ1) * v 1, v 2] := by
    funext i; fin_cases i
    · simp [rot01Matrix, Matrix.mulVec, Matrix.cons_val_zero, Matrix.vecHead,
        Matrix.vecTail]; ring
    · simp [rot01Matrix, Matrix.mulVec, Matrix.cons_val_one, Matrix.vecHead,
        Matrix.vecTail]
    · simp [rot01Matrix, Matrix.mulVec, Matrix.cons_val_two, Matrix.vecHead,
        Matrix.vecTail]
  have h2 : rot02Matrix (1 * θ2) *ᵥ ![Real.cos (1 * θ1) * v 0 - Real.sin (1 * θ1) * v 1,
      Real.sin (1 * θ1) * v 0 + Real.cos (1 * θ1) * v 1, v 2]
      = ![0, Real.sin (1 * θ1) * v 0 + Real.cos (1 * θ1) * v 1,
          Real.sin (1 * θ2) * (Real.cos (1 * θ1) * v 0 - Real.sin (1 * θ1) * v 1)
            + Real.cos (1 * θ2) * v 2] := by
    funext i; fin_cases i
    · simp [rot02Matrix, Matrix.mulVec, Matrix.cons_val_zero, Matrix.vecHead,
        Matrix.vecTail]; linear_combination hd0
    · simp [rot02Matrix, Matrix.mulVec, Matrix.cons_val_one, Matrix.vecHead,
        Matrix.vecTail]
    · simp [rot02Matrix, Matrix.mulVec, Matrix.cons_val_two, Matrix.vecHead,
        Matrix.vecTail]
  -- squared-norm preservation, instantiated with `x = y = v`
  have hn : (∑ i, (rotTriple 1 θ1 θ2 θ3 v) i * (rotTriple 1 θ1 θ2 θ3 v) i) = 1 := by
    have := BookSixth.threefold_rotation_preserves_inner_product
      (1:ℝ) (1*θ1) (1*θ2) (1*θ3) v v
    simpa [rotTriple, hv] using this
  rw [h1, h2]
  -- the third coordinate is forced by squared-norm preservation
  have hz : ((rot12Matrix (1 * θ3)).mulVec ![0,
      Real.sin (1 * θ1) * v 0 + Real.cos (1 * θ1) * v 1,
      Real.sin (1 * θ2) * (Real.cos (1 * θ1) * v 0 - Real.sin (1 * θ1) * v 1)
        + Real.cos (1 * θ2) * v 2]) 2 = 0 := by
    have hc0 : ((rot12Matrix (1 * θ3)).mulVec ![0,
        Real.sin (1 * θ1) * v 0 + Real.cos (1 * θ1) * v 1,
        Real.sin (1 * θ2) * (Real.cos (1 * θ1) * v 0 - Real.sin (1 * θ1) * v 1)
          + Real.cos (1 * θ2) * v 2]) 0 = 0 := by
      simp [rot12Matrix, Matrix.mulVec, Matrix.cons_val_zero, Matrix.vecHead,
        Matrix.vecTail]
    have hc1 : ((rot12Matrix (1 * θ3)).mulVec ![0,
        Real.sin (1 * θ1) * v 0 + Real.cos (1 * θ1) * v 1,
        Real.sin (1 * θ2) * (Real.cos (1 * θ1) * v 0 - Real.sin (1 * θ1) * v 1)
          + Real.cos (1 * θ2) * v 2]) 1 = 1 := by
      simp [rot12Matrix, Matrix.mulVec, Matrix.cons_val_one, Matrix.vecHead,
        Matrix.vecTail]
      linear_combination hρ3
    have hn' : (∑ i, ((rot12Matrix (1 * θ3)).mulVec
        ![0, Real.sin (1 * θ1) * v 0 + Real.cos (1 * θ1) * v 1,
          Real.sin (1 * θ2) * (Real.cos (1 * θ1) * v 0 - Real.sin (1 * θ1) * v 1)
            + Real.cos (1 * θ2) * v 2]) i
          * ((rot12Matrix (1 * θ3)).mulVec
        ![0, Real.sin (1 * θ1) * v 0 + Real.cos (1 * θ1) * v 1,
          Real.sin (1 * θ2) * (Real.cos (1 * θ1) * v 0 - Real.sin (1 * θ1) * v 1)
            + Real.cos (1 * θ2) * v 2]) i) = 1 := by
      have hcopy := hn
      rw [show rotTriple 1 θ1 θ2 θ3 v = ((rot12Matrix (1 * θ3)).mulVec
        (rot02Matrix (1 * θ2) *ᵥ (rot01Matrix (1 * θ1) *ᵥ v))) from rfl,
        h1, h2] at hcopy
      exact hcopy
    exact third_zero _ hn' hc0 hc1
  funext i; fin_cases i
  · simp [rot12Matrix, Matrix.mulVec, Matrix.cons_val_zero, Matrix.vecHead, Matrix.vecTail]
  · simp [rot12Matrix, Matrix.mulVec, Matrix.cons_val_one, Matrix.vecHead, Matrix.vecTail]
    linear_combination hρ3
  · exact hz
