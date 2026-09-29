-- Prove2me | solution 1 for KServer.workFnU_growth_two_server_start_inj
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-07T20:34:42.646434+00:00
-- url     : https://prove2.me/submissions/35e2cf9c-28e4-487d-aca8-fcf023e4ee0f

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Theorems.Thm_KServer_workFnU_growth_transfer_injective_start
import Theorems.Thm_KServer_workFnU_growth_two_server_inj

open KServer

theorem solution (M : Type) [MetricSpace M]
    (C₀ : Config 2 M) (hC₀ : Function.Injective C₀) :
    ∃ c : ℝ, ∀ σ : List M, ∃ u : ℕ → ℝ,
      (∀ t : ℕ, t < σ.length → ∀ X : Config 2 M,
          workFnU C₀ (σ.take (t + 1)) X ≤ workFnU C₀ (σ.take t) X + u t) ∧
      (∑ t ∈ Finset.range σ.length, u t) ≤ 3 * offlineCost C₀ σ + c := by
  obtain ⟨c, hc⟩ := workFnU_growth_two_server_inj M C₀
  refine ⟨c, fun σ => ?_⟩
  obtain ⟨u, h1, h2⟩ := hc σ
  exact ⟨u, fun t ht => workFnU_growth_transfer_injective_start 2 (by norm_num) M C₀ hC₀ _ _ _ (h1 t ht), h2⟩
