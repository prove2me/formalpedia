-- Prove2me | solution 1 for KServer.finite_game_uniform_value_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Wenqian Xing
-- created : 2026-09-06T16:50:35.525548+00:00
-- url     : https://prove2.me/submissions/8c3fcb64-859c-4399-8645-0e9795a96465
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_KServer_finite_game_bound_of_work_potential
import Theorems.Thm_KServer_workFnU_sharp_potential

set_option autoImplicit false
open KServer

theorem solution
    (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M] (C₀ : Config k M) :
    ∃ a : ℝ, ∀ P : Finset M, ∀ n : ℕ,
      finiteGameValue hk P (fun σ => (k : ℝ) * offlineCost C₀ σ) n [] C₀ ≤ a := by
  obtain ⟨Φ, c, hupper, hstep⟩ := KServer.workFnU_sharp_potential k hk M C₀
  exact KServer.finite_game_bound_of_work_potential k hk M C₀ (k : ℝ)
    (Nat.cast_nonneg k) Φ c hupper hstep
