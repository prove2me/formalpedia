-- Prove2me | solution 1 for KServer.workFnU_growth_card_add_two_start_inj
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-07T20:37:26.111293+00:00
-- url     : https://prove2.me/submissions/409b5ec2-3b04-48b1-a377-b287bbd25f7c

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Theorems.Thm_KServer_workFnU_growth_transfer_injective_start
import Theorems.Thm_KServer_workFnU_growth_card_add_two_inj

open KServer

theorem solution (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    [Fintype M] (hM : Fintype.card M = k + 2) (C₀ : Config k M)
    (hC₀ : Function.Injective C₀) :
    ∃ c : ℝ, ∀ σ : List M, ∃ u : ℕ → ℝ,
      (∀ t : ℕ, t < σ.length → ∀ X : Config k M,
          workFnU C₀ (σ.take (t + 1)) X ≤ workFnU C₀ (σ.take t) X + u t) ∧
      (∑ t ∈ Finset.range σ.length, u t) ≤ ((k : ℝ) + 1) * offlineCost C₀ σ + c := by
  obtain ⟨c, hc⟩ := workFnU_growth_card_add_two_inj k hk M hM C₀
  refine ⟨c, fun σ => ?_⟩
  obtain ⟨u, h1, h2⟩ := hc σ
  exact ⟨u, fun t ht => workFnU_growth_transfer_injective_start k hk M C₀ hC₀ _ _ _ (h1 t ht), h2⟩
