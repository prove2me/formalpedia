-- Prove2me | solution 1 for KServer.schedule_exists
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T03:48:32.239554+00:00
-- url     : https://prove2.me/submissions/fa76d98e-1322-4ad1-b58b-c7c6c766dbca

import Mathlib
import Definitions.Def_KServer_model

open KServer

theorem solution (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) : ∃ S : ℕ → Config k M, ServesFrom C₀ σ S := by
  classical
  have hk0 : (0 : ℕ) < k := hk
  refine ⟨fun j => if j = 0 then C₀ else fun _ => σ.getD (j - 1) (C₀ ⟨0, hk0⟩), by simp, ?_⟩
  intro j
  refine ⟨⟨0, hk0⟩, ?_⟩
  simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
  rw [List.getD_eq_getElem σ _ j.2]
  simp
