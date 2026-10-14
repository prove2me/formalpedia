-- Prove2me | solution 1 for KServer.workFnU_growth_sharp_large
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Wenqian Xing
-- created : 2026-09-06T17:47:02.794013+00:00
-- url     : https://prove2.me/submissions/b2e0e297-434f-441d-be3f-f4827b9881b1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_KServer_growth_bound_of_uniform_finite_subspaces
import Theorems.Thm_KServer_workFnU_growth_sharp_finite_subspaces
open KServer
set_option autoImplicit false

theorem solution
    (k : ℕ) (hk : 3 ≤ k) (M : Type) [MetricSpace M] (C₀ : Config k M)
    (hM : ∃ f : Fin (k + 3) → M, Function.Injective f) :
    ∃ c : ℝ, ∀ σ : List M, ∃ u : ℕ → ℝ,
      (∀ t : ℕ, t < σ.length → ∀ X : Config k M, Function.Injective X →
        workFnU C₀ (σ.take (t + 1)) X ≤ workFnU C₀ (σ.take t) X + u t) ∧
      (∑ t ∈ Finset.range σ.length, u t) ≤ ((k : ℝ) + 1) * offlineCost C₀ σ + c := by
  obtain ⟨c, hc⟩ := KServer.workFnU_growth_sharp_finite_subspaces k hk M C₀ hM
  obtain ⟨f, hf⟩ := hM
  have hi : ∃ X : Config k M, Function.Injective X :=
    ⟨fun i => f (Fin.castLE (by omega : k ≤ k + 3) i),
      hf.comp (Fin.castLE_injective (by omega : k ≤ k + 3))⟩
  exact ⟨c, KServer.growth_bound_of_uniform_finite_subspaces k (by omega) M C₀
    ((k : ℝ) + 1) c (by positivity) hi hc⟩
