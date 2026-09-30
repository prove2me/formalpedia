-- Prove2me | solution 1 for lean_workbook_plus_29816
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:06:40.302633+00:00
-- url     : https://prove2.me/submissions/52f46372-4764-4ce5-947a-033c9f7f2c9c

import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Finset.Card
import Mathlib.Order.Bounds.Defs
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

def footballRoster (t : Fin 18) : Finset (Fin 18) :=
  Finset.univ.filter (fun p => (p.val + 18 - t.val) % 18 < 11)

def footballPlayingSlots (p : Fin 18) : Finset (Fin 18) :=
  Finset.univ.filter (fun t => p ∈ footballRoster t)

theorem football_roster_card : ∀ t : Fin 18, (footballRoster t).card = 11 := by
  decide

theorem football_playing_slots_card :
    ∀ p : Fin 18, (footballPlayingSlots p).card = 11 := by
  decide

theorem football_single_substitution : ∀ t : Fin 17,
    footballRoster ⟨t.val + 1, by omega⟩ =
      insert ⟨(t.val + 11) % 18, Nat.mod_lt _ (by decide)⟩
        ((footballRoster ⟨t.val, by omega⟩).erase ⟨t.val, by omega⟩) := by
  decide

private theorem football_player_lower_bound (n k : ℕ)
    (hk : k < 60) (hproduct : n * k = 90 * 11) : 18 ≤ n := by
  have hk59 : k ≤ 59 := by omega
  have hbound := Nat.mul_le_mul_left n hk59
  have hn17 : 17 ≤ n := by nlinarith
  by_contra h
  have hn : n = 17 := by omega
  subst n
  omega

theorem football_minimum_and_schedule :
    IsLeast {n : ℕ | ∃ k : ℕ, 0 < n ∧ 0 < k ∧ k < 60 ∧ n * k = 90 * 11} 18 ∧
    5 * Fintype.card (Fin 18) = 90 ∧
    (∀ t : Fin 18, (footballRoster t).card = 11) ∧
    (∀ p : Fin 18, 5 * (footballPlayingSlots p).card = 55) ∧
    (∀ t : Fin 17,
      footballRoster ⟨t.val + 1, by omega⟩ =
        insert ⟨(t.val + 11) % 18, Nat.mod_lt _ (by decide)⟩
          ((footballRoster ⟨t.val, by omega⟩).erase ⟨t.val, by omega⟩)) := by
  refine ⟨?_, by decide, football_roster_card, ?_, football_single_substitution⟩
  · constructor
    · exact ⟨55, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · rintro n ⟨k, _, _, hk, hproduct⟩
      exact football_player_lower_bound n k hk hproduct
  · intro p
    rw [football_playing_slots_card]

theorem solution (n k : ℕ) (h₀ : 0 < n ∧ 0 < k) (h₁ : k < 60)
    (h₂ : n * k = 90 * 11) : 18 ≤ n :=
  football_minimum_and_schedule.1.2 ⟨k, h₀.1, h₀.2, h₁, h₂⟩
