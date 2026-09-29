-- Prove2me | solution 1 for Bishop.constructive_sup
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T13:51:51.653724+00:00
-- url     : https://prove2.me/submissions/bd537e12-714f-4efb-887b-386a82e5c7a7

import Mathlib
import Definitions.Def_Logic_ConstructiveAnalysis_BishopReals
import Definitions.Def_Logic_ConstructiveAnalysis_ConstructiveSup

open Bishop Set in
theorem solution {S : Set ℝ} (D : LocatedData S) {a₀ b₀ : ℚ} (hab : a₀ < b₀)
    (h₀ : Enclosing S (a₀, b₀)) :
    ∃ u : ℝ, IsLUB S u ∧ ∀ n : ℕ,
      ((bisect D.L a₀ b₀ n).1 : ℝ) ≤ u ∧ u ≤ ((bisect D.L a₀ b₀ n).2 : ℝ) ∧
        ((bisect D.L a₀ b₀ n).2 : ℝ) - ((bisect D.L a₀ b₀ n).1 : ℝ)
          = (2 / 3 : ℝ) ^ n * ((b₀ : ℝ) - (a₀ : ℝ)) := by
  -- the search keeps a proper enclosure whose width shrinks by `2/3` per step
  have inv : ∀ n, (bisect D.L a₀ b₀ n).1 < (bisect D.L a₀ b₀ n).2 ∧
      Enclosing S (bisect D.L a₀ b₀ n) ∧
      (bisect D.L a₀ b₀ n).2 - (bisect D.L a₀ b₀ n).1 = (2 / 3 : ℚ) ^ n * (b₀ - a₀) := by
    intro n
    induction n with
    | zero => exact ⟨hab, h₀, by simp [bisect]⟩
    | succ n ih =>
      rw [show bisect D.L a₀ b₀ (n + 1) = bisectStep D.L (bisect D.L a₀ b₀ n) from rfl]
      generalize bisect D.L a₀ b₀ n = pq at ih ⊢
      obtain ⟨p, q⟩ := pq
      obtain ⟨hlt, ⟨hup, s, hs, hps⟩, hw⟩ := ih
      simp only at hlt hup hps hw
      have hm : p + (q - p) / 3 < p + 2 * (q - p) / 3 := by linarith
      cases hL : D.L (p + (q - p) / 3) (p + 2 * (q - p) / 3)
      · have hstep : bisectStep D.L (p, q) = (p + (q - p) / 3, q) := by
          simp only [bisectStep, hL, Bool.false_eq_true, if_false]
        rw [hstep]
        refine ⟨by linarith, ⟨hup, D.witness _ _ hm hL⟩, ?_⟩
        rw [pow_succ]
        linear_combination (2 / 3 : ℚ) * hw
      · have hstep : bisectStep D.L (p, q) = (p, p + 2 * (q - p) / 3) := by
          simp only [bisectStep, hL, if_true]
        rw [hstep]
        refine ⟨by linarith, ⟨D.upper _ _ hm hL, s, hs, hps⟩, ?_⟩
        rw [pow_succ]
        linear_combination (2 / 3 : ℚ) * hw
  obtain ⟨-, ⟨hup0, s0, hs0, -⟩, -⟩ := inv 0
  have hne : S.Nonempty := ⟨s0, hs0⟩
  have hbdd : BddAbove S := ⟨(b₀ : ℝ), fun s hs => hup0 s hs⟩
  refine ⟨sSup S, isLUB_csSup hne hbdd, fun n => ?_⟩
  obtain ⟨-, ⟨hup, s, hs, hps⟩, hw⟩ := inv n
  refine ⟨(hps.trans_le (le_csSup hbdd hs)).le, csSup_le hne hup, ?_⟩
  have hw' := congrArg (fun t : ℚ => (t : ℝ)) hw
  push_cast at hw'
  exact hw'
