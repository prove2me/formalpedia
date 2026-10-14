-- Prove2me | solution 1 for KServer.workFnU_sharp_potential_known_cases
-- status  : ACCEPTED   (prove)
-- author  : @Wenqian Xing
-- created : 2026-09-06T17:11:55.498928+00:00
-- url     : https://prove2.me/submissions/1e9f3a8c-329f-4443-bbb2-f4eafed5f981

import Theorems.Thm_HistoryPotential_pathwise_bound_iff
import Theorems.Thm_KServer_workFnU_growth_two_server_inj
import Theorems.Thm_KServer_workFnU_growth_2k_inj
import Theorems.Thm_KServer_workFnU_growth_card_add_two_inj
import Theorems.Thm_KServer_workFnU_growth_card_succ_inj
import Theorems.Thm_KServer_workFnU_step_le

set_option autoImplicit false
open KServer

private lemma offline_nonneg {k : ℕ} {M : Type} [MetricSpace M]
    (C₀ : Config k M) (σ : List M) : 0 ≤ offlineCost C₀ σ := by
  apply Real.sInf_nonneg
  rintro c ⟨S, _, rfl⟩
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => dist_nonneg

theorem solution (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M)
    (hsmall : k ≤ 2 ∨ ¬ ∃ f : Fin (k + 3) → M, Function.Injective f) :
    ∃ Φ : List M → ℝ, ∃ c : ℝ,
      (∀ σ : List M, Φ σ ≤ ((k : ℝ) + 1) * offlineCost C₀ σ + c) ∧
      (∀ (l : List M) (r : M) (X : Config k M), Function.Injective X →
        workFnU C₀ (l ++ [r]) X - workFnU C₀ l X ≤ Φ (l ++ [r]) - Φ l) := by
  classical
  by_cases hex : ∃ X : Config k M, Function.Injective X
  · have H : ∃ c : ℝ, ∀ σ : List M, ∃ u : ℕ → ℝ,
        (∀ t : ℕ, t < σ.length → ∀ X : Config k M, Function.Injective X →
          workFnU C₀ (σ.take (t + 1)) X ≤ workFnU C₀ (σ.take t) X + u t) ∧
        (∑ t ∈ Finset.range σ.length, u t) ≤ ((k : ℝ) + 1) * offlineCost C₀ σ + c := by
      rcases hsmall with hk2 | hM
      · have : k = 1 ∨ k = 2 := by omega
        rcases this with rfl | rfl
        · convert KServer.workFnU_growth_2k_inj 1 hk M C₀ using 1 <;> norm_num
        · convert KServer.workFnU_growth_two_server_inj M C₀ using 1 <;> norm_num
      · letI : Fintype M := fintypeOfNotInfinite (by
          intro hInf
          letI : Infinite M := hInf
          exact hM ⟨fun i => Infinite.natEmbedding M i.val,
            (Infinite.natEmbedding M).injective.comp Fin.val_injective⟩)
        have hcard : Fintype.card M ≤ k + 2 := by
          by_contra h
          have hle : k + 3 ≤ Fintype.card M := by omega
          exact hM ⟨fun i => (Fintype.equivFin M).symm (Fin.castLE hle i),
            (Fintype.equivFin M).symm.injective.comp (Fin.castLE_injective hle)⟩
        by_cases htwo : Fintype.card M = k + 2
        · exact KServer.workFnU_growth_card_add_two_inj k hk M htwo C₀
        by_cases hone : Fintype.card M = k + 1
        · exact KServer.workFnU_growth_card_succ_inj k hk M hone C₀
        have hle : Fintype.card M ≤ k := by omega
        refine ⟨0, fun σ => ⟨fun _ => 0, ?_, ?_⟩⟩
        · intro t ht X hX
          have hge : k ≤ Fintype.card M := by
            simpa using Fintype.card_le_of_injective X hX
          have hsurj : Function.Surjective X :=
            ((Fintype.bijective_iff_injective_and_card X).mpr
              ⟨hX, by simpa using le_antisymm hge hle⟩).2
          have hh := KServer.workFnU_step_le k hk M C₀ (σ.take t) σ[t] X X
            (hsurj σ[t])
          have heq : σ.take (t + 1) = σ.take t ++ [σ[t]] := by
            rw [List.take_add_one, List.getElem?_eq_getElem ht]
            rfl
          rw [heq]
          simpa only [moveCost, dist_self, Finset.sum_const_zero, add_zero] using hh
        · simpa using mul_nonneg (by positivity : 0 ≤ (k : ℝ) + 1)
            (offline_nonneg C₀ σ)
    obtain ⟨c, H⟩ := H
    letI : Nonempty {X : Config k M // Function.Injective X} :=
      ⟨⟨hex.choose, hex.choose_spec⟩⟩
    obtain ⟨Φ, _, hupper, hstep⟩ :=
      (HistoryPotential.pathwise_bound_iff M {X : Config k M // Function.Injective X}
        (fun l X => workFnU C₀ l X.val)
        (fun σ => ((k : ℝ) + 1) * offlineCost C₀ σ + c)).mpr (by
          intro σ
          obtain ⟨u, hu, hsum⟩ := H σ
          exact ⟨u, fun t ht X => hu t ht X.val X.property, hsum⟩)
    exact ⟨Φ, c, hupper, fun l r X hX => hstep l r ⟨X, hX⟩⟩
  · refine ⟨fun _ => 0, 0, ?_, ?_⟩
    · intro σ
      simpa using mul_nonneg (by positivity : 0 ≤ (k : ℝ) + 1) (offline_nonneg C₀ σ)
    · intro l r X hX
      exact (hex ⟨X, hX⟩).elim

#print axioms solution
