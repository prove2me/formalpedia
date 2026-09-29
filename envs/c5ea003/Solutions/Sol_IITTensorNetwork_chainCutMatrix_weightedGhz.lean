-- Prove2me | solution 1 for IITTensorNetwork.chainCutMatrix_weightedGhz
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-21T02:29:34.845581+00:00
-- url     : https://prove2.me/submissions/9ab8ee39-a96e-4e9f-a6f4-156f3fef81e0

import Mathlib
import Definitions.Def_Novelty_IITTensorNetworkPhi
import Definitions.Def_Novelty_IITTensorNetworkSchmidtSpectrum
import Definitions.Def_Novelty_IITTensorNetworkWeightedGHZ

set_option maxHeartbeats 2000000 in
open Finset Matrix IITTensorNetwork in
theorem solution {n d : ℕ} {w : Fin d → ℝ} {l : ℕ} (hl : l ≤ n) :
    chainCutMatrix (weightedGhzState n d w) l hl
      = wMaxEnt w (constCfg l d) (constCfg (n - l) d) := by
  classical
  -- a glued configuration is constant exactly when both halves are constant with the same letter
  have hglue : ∀ (f : Fin l → Fin d) (g : Fin (n - l) → Fin d) (x : Fin d),
      (glue l hl f g = constCfg n d x) ↔ (constCfg l d x = f ∧ constCfg (n - l) d x = g) := by
    intro f g x
    constructor
    · intro h
      refine ⟨funext (fun j => ?_), funext (fun j => ?_)⟩
      · have hj : (j : ℕ) < n := by have := j.isLt; omega
        have hx := congrFun h ⟨(j : ℕ), hj⟩
        simpa [glue, constCfg, j.isLt] using hx.symm
      · have hj : l + (j : ℕ) < n := by have := j.isLt; omega
        have hx := congrFun h ⟨l + (j : ℕ), hj⟩
        simp only [glue, constCfg, dif_neg (by omega : ¬ (l + (j : ℕ) < l))] at hx
        simpa [constCfg] using hx.symm
    · rintro ⟨rfl, rfl⟩
      funext i
      by_cases hi : (i : ℕ) < l <;> simp [glue, constCfg, hi]
  ext f g
  simp only [chainCutMatrix, Matrix.of_apply, weightedGhzState, wMaxEnt, Matrix.mul_apply,
    Matrix.diagonal_apply, Matrix.conjTranspose_apply, isoMatrix, mul_ite, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  by_cases hx : glue l hl f g = constCfg n d x
  · obtain ⟨h1, h2⟩ := (hglue f g x).mp hx
    simp [hx, h1, h2]
  · have hn2 := (hglue f g x).not.mp hx
    rw [if_neg hx]
    by_cases h1 : constCfg l d x = f
    · have h2 : ¬ (constCfg (n - l) d x = g) := fun h => hn2 ⟨h1, h⟩
      simp [h1, h2]
    · simp [h1]
