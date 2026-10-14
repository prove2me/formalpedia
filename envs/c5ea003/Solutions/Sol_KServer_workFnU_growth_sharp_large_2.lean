-- Prove2me | solution 2 for KServer.workFnU_growth_sharp_large
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-07T05:00:40.037572+00:00
-- url     : https://prove2.me/submissions/adcdc8e0-618a-415e-8b5b-82ff6830f3a4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_KServer_workFnU_growth_sharp_finite_subspaces
import Theorems.Thm_KServer_growth_bound_of_uniform_finite_subspaces

open KServer

theorem solution
    (k : ℕ) (hk : 3 ≤ k) (M : Type) [MetricSpace M] (C₀ : Config k M)
    (hM : ∃ f : Fin (k + 3) → M, Function.Injective f) :
    ∃ c : ℝ, ∀ σ : List M, ∃ u : ℕ → ℝ,
      (∀ t : ℕ, t < σ.length → ∀ X : Config k M, Function.Injective X →
        workFnU C₀ (σ.take (t + 1)) X ≤ workFnU C₀ (σ.take t) X + u t) ∧
      (∑ t ∈ Finset.range σ.length, u t) ≤ ((k : ℝ) + 1) * offlineCost C₀ σ + c := by
  obtain ⟨c, hfinite⟩ := workFnU_growth_sharp_finite_subspaces k hk M C₀ hM
  refine ⟨c, ?_⟩
  have hI : ∃ X : Config k M, Function.Injective X := by
    obtain ⟨f, hf⟩ := hM
    let e : Fin k → Fin (k + 3) := fun i => ⟨i.val, by omega⟩
    have he : Function.Injective e := by
      intro i j hij
      apply Fin.ext
      exact congrArg (fun z : Fin (k + 3) => z.val) hij
    exact ⟨f ∘ e, hf.comp he⟩
  have hk1 : 1 ≤ k := by omega
  exact growth_bound_of_uniform_finite_subspaces k hk1 M C₀ ((k : ℝ) + 1) c
    (by positivity) hI hfinite
