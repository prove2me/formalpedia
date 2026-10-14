-- Prove2me | solution 1 for KServer.finite_horizon_uniform_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Wenqian Xing
-- created : 2026-09-06T15:23:31.796939+00:00
-- url     : https://prove2.me/submissions/9c4725f6-45e3-4e79-9bfd-6b7553c1ff0d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_KServer_finite_game_characterization
import Theorems.Thm_KServer_finite_game_uniform_value_bound

set_option autoImplicit false
open KServer

/-- The original target follows from the scalar uniform bound using the
proved finite-game characterization. The scalar bound remains open. -/
theorem solution
    (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M] (C₀ : Config k M) :
    ∃ a : ℝ, ∀ P : Finset M, ∀ n : ℕ,
      ∃ A : OnlineAlgorithm k M, A.conf [] = C₀ ∧
        ∀ σ : List M, σ.length ≤ n → (∀ r ∈ σ, r ∈ P) →
          A.cost σ ≤ (k : ℝ) * offlineCost C₀ σ + a := by
  obtain ⟨a, ha⟩ := KServer.finite_game_uniform_value_bound k hk M C₀
  refine ⟨a, fun P n => ?_⟩
  exact (KServer.finite_game_characterization k hk M C₀ P
    (fun σ => (k : ℝ) * offlineCost C₀ σ) n a).mp (ha P n)

#print axioms solution
