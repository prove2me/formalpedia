-- Prove2me | solution 1 for KServer.finite_game_bound_of_work_potential
-- status  : ACCEPTED   (prove)
-- author  : @Wenqian Xing
-- created : 2026-09-06T16:48:29.641712+00:00
-- url     : https://prove2.me/submissions/aa4d6e31-47fe-4df9-8b93-3523e85eb312

import Theorems.Thm_KServer_extended_cost_lemma_injective
import Theorems.Thm_KServer_injective_or_covering
import Theorems.Thm_KServer_competitive_of_covering_config
import Theorems.Thm_KServer_finite_game_characterization

set_option autoImplicit false
open KServer

/-- A potential dominating every injective work-function increment gives a
uniform bound for all finite games. The rate and potential are explicit inputs. -/
theorem solution (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (ρ : ℝ) (hρ : 0 ≤ ρ) (Φ : List M → ℝ) (c : ℝ)
    (hupper : ∀ σ : List M, Φ σ ≤ (ρ + 1) * offlineCost C₀ σ + c)
    (hstep : ∀ (l : List M) (r : M) (X : Config k M), Function.Injective X →
      workFnU C₀ (l ++ [r]) X - workFnU C₀ l X ≤ Φ (l ++ [r]) - Φ l) :
    ∃ a : ℝ, ∀ P : Finset M, ∀ n : ℕ,
      finiteGameValue hk P (fun σ => ρ * offlineCost C₀ σ) n [] C₀ ≤ a := by
  have halg : ∃ A : OnlineAlgorithm k M,
      A.conf [] = C₀ ∧ IsCompetitive A ρ := by
    rcases KServer.injective_or_covering k M C₀ with ⟨X₀, hX₀⟩ | ⟨Y, hY⟩
    · have hsum (σ : List M) : ∃ u : ℕ → ℝ,
          (∀ t : ℕ, t < σ.length → ∀ X : Config k M, Function.Injective X →
            workFnU C₀ (σ.take (t + 1)) X ≤ workFnU C₀ (σ.take t) X + u t) ∧
          (∑ t ∈ Finset.range σ.length, u t) ≤
            (ρ + 1) * offlineCost C₀ σ + (c - Φ []) := by
        refine ⟨fun t => Φ (σ.take (t + 1)) - Φ (σ.take t), ?_, ?_⟩
        · intro t ht X hX
          have heq : σ.take (t + 1) = σ.take t ++ [σ[t]] := by
            rw [List.take_add_one, List.getElem?_eq_getElem ht]
            rfl
          have hh := hstep (σ.take t) σ[t] X hX
          rw [← heq] at hh
          linarith
        · rw [Finset.sum_range_sub (fun t => Φ (σ.take t))]
          simp only [List.take_length, List.take_zero]
          linarith [hupper σ]
      obtain ⟨A, hA0, hA⟩ := KServer.extended_cost_lemma_injective k hk M C₀ X₀ hX₀
        (ρ + 1) (c - Φ []) hsum
      refine ⟨A, hA0, ?_⟩
      simpa only [add_sub_cancel_right] using hA
    · exact KServer.competitive_of_covering_config k M C₀ Y hY ρ hρ
  obtain ⟨A, hA0, a, hA⟩ := halg
  refine ⟨a, fun P n => ?_⟩
  apply (KServer.finite_game_characterization k hk M C₀ P
    (fun σ => ρ * offlineCost C₀ σ) n a).mpr
  refine ⟨A, hA0, fun σ _ _ => ?_⟩
  simpa only [hA0] using hA σ

