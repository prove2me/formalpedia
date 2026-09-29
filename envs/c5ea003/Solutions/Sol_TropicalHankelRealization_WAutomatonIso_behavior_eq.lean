-- Prove2me | solution 1 for TropicalHankelRealization.WAutomatonIso.behavior_eq
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T18:39:46.032569+00:00
-- url     : https://prove2.me/submissions/000a11b7-4a62-4303-a5b5-a403ac9b69ea

import Mathlib
import Definitions.Def_Bridges_TropicalHankelRealizationDuality
open Finset BigOperators TropicalHankelRealization in
theorem solution {K : Type*} [CommSemiring K] {A : Type*} {n m : ℕ}
    {T₁ : WAutomaton K A n} {T₂ : WAutomaton K A m}
    (iso : WAutomatonIso T₁ T₂) : T₁.behavior = T₂.behavior := by
  -- one step commutes with the state relabelling
  have hstep : ∀ (v₁ : Fin n → K) (v₂ : Fin m → K), (∀ i, v₂ (iso.stateEquiv i) = v₁ i) →
      ∀ a j, T₂.step v₂ a (iso.stateEquiv j) = T₁.step v₁ a j := by
    intro v₁ v₂ hv a j
    unfold WAutomaton.step
    rw [← iso.stateEquiv.sum_comp]
    exact sum_congr rfl (fun i _ => by rw [hv i, iso.trans_compat])
  -- hence so does every run
  have hfold : ∀ (w : List A) (v₁ : Fin n → K) (v₂ : Fin m → K),
      (∀ i, v₂ (iso.stateEquiv i) = v₁ i) →
        ∀ j, w.foldl T₂.step v₂ (iso.stateEquiv j) = w.foldl T₁.step v₁ j := by
    intro w
    induction w with
    | nil =>
      intro v₁ v₂ hv j
      exact hv j
    | cons a w ih =>
      intro v₁ v₂ hv j
      exact ih _ _ (hstep v₁ v₂ hv a) j
  funext w
  unfold WAutomaton.behavior WAutomaton.reach
  rw [← iso.stateEquiv.sum_comp]
  refine sum_congr rfl (fun j _ => ?_)
  rw [hfold w T₁.init T₂.init iso.init_compat j, iso.output_compat]
