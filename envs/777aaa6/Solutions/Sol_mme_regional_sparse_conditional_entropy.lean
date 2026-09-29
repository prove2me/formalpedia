-- Prove2me | solution 1 for mme_regional_sparse_conditional_entropy
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-13T20:34:05.397715+00:00
-- url     : https://prove2.me/submissions/4d566406-9a03-4438-be0c-b8a6be421646

import Definitions.Def_mme_regional_entropy_rate_data
import Mathlib
open BigOperators MME.RegionRate
set_option autoImplicit false
set_option maxHeartbeats 1000000

private theorem one_column {J : Type*} [Fintype J] (x : J → ℝ)
    (h : ∀ j k, x j ≠ 0 → x k ≠ 0 → j = k) :
    ∑ j, Real.negMulLog (x j) = Real.negMulLog (∑ j, x j) := by
  classical
  by_cases hz : ∀ j, x j = 0
  · simp [hz]
  · obtain ⟨j,hj⟩ := not_forall.mp hz
    have hk (k : J) (hne : k ≠ j) : x k = 0 := by
      by_contra hn
      exact hne (h k j hn hj)
    rw [Finset.sum_eq_single j,Finset.sum_eq_single j]
    · intro k _ hkj; exact hk k hkj
    · simp
    · intro k _ hkj; simp [hk k hkj]
    · simp

theorem solution {J W : Type*} [Fintype J] [Fintype W] (x : J → W → ℝ)
    (hsparse : ∀ w j k, x j w ≠ 0 → x k w ≠ 0 → j = k) :
    (∑ j, massEntropy (x j)) =
      massEntropy (fun w ↦ ∑ j, x j w) - massEntropy (fun j ↦ ∑ w, x j w) := by
  have he : (∑ j, entropy (x j)) = entropy (fun w ↦ ∑ j, x j w) := by
    unfold entropy
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    exact fun w _ ↦ one_column (fun j ↦ x j w) (hsparse w)
  simp only [massEntropy,Finset.sum_sub_distrib]
  rw [he]
  unfold entropy
  rw [Finset.sum_comm (f := fun w j ↦ x j w)]
  ring
