-- Prove2me | solution 1 for MarkovMixing.detailed_balance_stationary
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-08-22T03:05:59.656045+00:00
-- url     : https://prove2.me/submissions/1064f13d-c728-489e-80f1-13521dec9fbf

import Definitions.Def_mm_basic

open scoped BigOperators
open MarkovMixing

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (π : V → ℝ) (hπ : IsDist π)
    (hdb : DetailedBalance P π) :
    IsStationary P π := by
  refine ⟨hπ, ?_⟩
  funext x
  have : (Matrix.vecMul π P) x = ∑ y, π y * P y x := rfl
  rw [this]
  have h1 : ∀ y : V, π y * P y x = π x * P x y := fun y => (hdb x y).symm
  rw [Finset.sum_congr rfl (fun y _ => h1 y), ← Finset.mul_sum, hP.2 x, mul_one]
