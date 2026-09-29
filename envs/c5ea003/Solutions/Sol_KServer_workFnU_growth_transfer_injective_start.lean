-- Prove2me | solution 1 for KServer.workFnU_growth_transfer_injective_start
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-07T20:31:16.827713+00:00
-- url     : https://prove2.me/submissions/1e55bb23-9856-456a-8c8f-41a110efb5f1

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Theorems.Thm_KServer_workFnU_lipschitz
import Theorems.Thm_KServer_workFnU_injective_witness

open KServer

theorem solution (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (hC₀ : Function.Injective C₀) (σ₁ σ₂ : List M) (u : ℝ)
    (h : ∀ X : Config k M, Function.Injective X →
        workFnU C₀ σ₂ X ≤ workFnU C₀ σ₁ X + u) :
    ∀ X : Config k M, workFnU C₀ σ₂ X ≤ workFnU C₀ σ₁ X + u := by
  intro Y
  refine le_of_forall_pos_le_add ?_
  intro ε hε
  obtain ⟨X, hXinj, hX⟩ := workFnU_injective_witness k hk M C₀ hC₀ σ₁ Y ε hε
  have hlip : workFnU C₀ σ₂ Y ≤ workFnU C₀ σ₂ X + moveCost X Y :=
    workFnU_lipschitz k hk M C₀ σ₂ Y X
  have hgr := h X hXinj
  linarith
