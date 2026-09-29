-- Prove2me | solution 1 for IITTensorNetwork.norm_sq_weightedGhzState
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-21T02:26:05.145439+00:00
-- url     : https://prove2.me/submissions/b16772f1-1249-4d92-899f-6ed1f27490ce

import Mathlib
import Definitions.Def_Novelty_IITTensorNetworkPhi
import Definitions.Def_Novelty_IITTensorNetworkSchmidtSpectrum
import Definitions.Def_Novelty_IITTensorNetworkWeightedGHZ

set_option maxHeartbeats 2000000 in
open Finset Matrix IITTensorNetwork in
theorem solution {n d : ℕ} {w : Fin d → ℝ} (hn : 1 ≤ n) (s : Fin n → Fin d) :
    ‖weightedGhzState n d w s‖ ^ 2 = ∑ x, if s = constCfg n d x then w x ^ 2 else 0 := by
  classical
  -- with at least one site, distinct letters give distinct constant configurations
  have hinj : Function.Injective (constCfg n d) := by
    intro x y hxy
    simpa [constCfg] using congrFun hxy ⟨0, by omega⟩
  by_cases hex : ∃ x0, s = constCfg n d x0
  · obtain ⟨x0, rfl⟩ := hex
    have h1 : weightedGhzState n d w (constCfg n d x0) = (w x0 : ℂ) := by
      simp only [weightedGhzState, hinj.eq_iff]
      rw [Finset.sum_ite_eq]
      simp
    rw [h1]
    simp only [hinj.eq_iff]
    rw [Finset.sum_ite_eq]
    simp [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  · push_neg at hex
    have h1 : weightedGhzState n d w s = 0 := by
      simp only [weightedGhzState]
      exact Finset.sum_eq_zero (fun x _ => if_neg (hex x))
    rw [h1, Finset.sum_eq_zero (fun x _ => if_neg (hex x))]
    simp
