-- Prove2me | solution 1 for KServer.workFnU_sharp_potential
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Wenqian Xing
-- created : 2026-09-06T17:14:30.541049+00:00
-- url     : https://prove2.me/submissions/6c21c07d-4ab7-4843-ad0c-bf679b097b57
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_HistoryPotential_pathwise_bound_iff
import Theorems.Thm_KServer_workFnU_sharp_potential_known_cases
import Theorems.Thm_KServer_workFnU_growth_sharp_large

set_option autoImplicit false
open KServer

theorem solution
    (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M] (C₀ : Config k M) :
    ∃ Φ : List M → ℝ, ∃ c : ℝ,
      (∀ σ : List M, Φ σ ≤ ((k : ℝ) + 1) * offlineCost C₀ σ + c) ∧
      (∀ (l : List M) (r : M) (X : Config k M), Function.Injective X →
        workFnU C₀ (l ++ [r]) X - workFnU C₀ l X ≤ Φ (l ++ [r]) - Φ l) := by
  classical
  by_cases hs : k ≤ 2 ∨ ¬ ∃ f : Fin (k + 3) → M, Function.Injective f
  · exact KServer.workFnU_sharp_potential_known_cases k hk M C₀ hs
  · have hk3 : 3 ≤ k := by omega
    have hM : ∃ f : Fin (k + 3) → M, Function.Injective f := by tauto
    obtain ⟨c, H⟩ := KServer.workFnU_growth_sharp_large k hk3 M C₀ hM
    obtain ⟨f, hf⟩ := hM
    let X : Config k M := fun i => f (Fin.castLE (by omega) i)
    have hX : Function.Injective X := hf.comp (Fin.castLE_injective (by omega))
    letI : Nonempty {Y : Config k M // Function.Injective Y} := ⟨⟨X, hX⟩⟩
    obtain ⟨Φ, _, hupper, hstep⟩ :=
      (HistoryPotential.pathwise_bound_iff M {Y : Config k M // Function.Injective Y}
        (fun l Y => workFnU C₀ l Y.val)
        (fun σ => ((k : ℝ) + 1) * offlineCost C₀ σ + c)).mpr (by
          intro σ
          obtain ⟨u, hu, hsum⟩ := H σ
          exact ⟨u, fun t ht Y => hu t ht Y.val Y.property, hsum⟩)
    exact ⟨Φ, c, hupper, fun l r Y hY => hstep l r ⟨Y, hY⟩⟩
