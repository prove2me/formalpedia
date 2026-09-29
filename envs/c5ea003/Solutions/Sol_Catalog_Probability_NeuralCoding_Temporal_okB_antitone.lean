-- Prove2me | solution 1 for Catalog.Probability.NeuralCoding.Temporal.okB_antitone
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T20:49:53.590843+00:00
-- url     : https://prove2.me/submissions/7ac49b07-8bb0-4b71-b931-b3b9e39ee972

import Mathlib
import Definitions.Def_Probability_RefractoryGeneralized
open Catalog.Probability.NeuralCoding.Temporal in
theorem solution {r s : ℕ} (h : r ≤ s) :
    ∀ l : List Bool, okB s l = true → okB r l = true := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons b l ih =>
    cases b with
    | false => exact ih
    | true =>
      -- a shorter refractory window is implied by a longer one
      intro hl
      simp only [okB, Bool.and_eq_true, List.all_eq_true] at hl ⊢
      exact ⟨fun x hx => hl.1 x (List.take_subset_take_left l h hx), ih hl.2⟩
