-- Prove2me | solution 1 for ForkPinning.sign_determined_balanced
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T23:30:45.933826+00:00
-- url     : https://prove2.me/submissions/52d1456d-0de6-4a70-8f32-eb796f807a2f

import Mathlib
import Definitions.Def_Probability_ForkPinningCore
import Definitions.Def_Probability_ForkPinningGalois
open ForkPinning Finset Real in
theorem solution {n : ℕ} (hn : 2 ≤ n) (Y : Equiv.Perm (Fin n) → Bool)
    (hdet : Determines (signBool : Equiv.Perm (Fin n) → Bool) Y)
    (hbal : prb Y true = 1 / 2) :
    Y = (signBool : Equiv.Perm (Fin n) → Bool) ∨
      Y = fun σ : Equiv.Perm (Fin n) => !(signBool σ) := by
  have hcard : (Fintype.card (Equiv.Perm (Fin n)) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  -- an even and an odd permutation
  have hi : (0 : ℕ) < n := by omega
  have hj : (1 : ℕ) < n := by omega
  set i : Fin n := ⟨0, hi⟩ with hidef
  set j : Fin n := ⟨1, hj⟩ with hjdef
  have hij : i ≠ j := by
    simp only [hidef, hjdef, Ne, Fin.mk.injEq]
    omega
  have hsb1 : signBool (1 : Equiv.Perm (Fin n)) = true := by
    simp [signBool]
  have hsbc : signBool (Equiv.swap i j) = false := by
    rw [signBool, Equiv.Perm.sign_swap hij]
    decide
  -- Y factors through the sign
  have hY : ∀ σ : Equiv.Perm (Fin n),
      Y σ = if signBool σ = true then Y 1 else Y (Equiv.swap i j) := by
    intro σ
    by_cases h : signBool σ = true
    · rw [if_pos h]
      exact hdet σ 1 (by rw [h, hsb1])
    · rw [if_neg h]
      rw [Bool.not_eq_true] at h
      exact hdet σ (Equiv.swap i j) (by rw [h, hsbc])
  rcases Bool.eq_false_or_eq_true (Y 1) with h1 | h1 <;>
    rcases Bool.eq_false_or_eq_true (Y (Equiv.swap i j)) with h2 | h2
  · -- Y 1 = true, Y c = true : constantly true, so prb Y true = 1
    exfalso
    have hconst : ∀ σ, Y σ = true := by
      intro σ
      rw [hY σ]
      by_cases h : signBool σ = true
      · rw [if_pos h]; exact h1
      · rw [if_neg h]; exact h2
    have he : fiber Y true = Finset.univ := by
      ext σ
      simp [fiber, hconst σ]
    rw [prb, he, Finset.card_univ, div_self hcard] at hbal
    norm_num at hbal
  · -- Y 1 = true, Y c = false : Y = signBool
    left
    funext σ
    rw [hY σ]
    by_cases h : signBool σ = true
    · rw [if_pos h, h1, h]
    · rw [if_neg h, h2]
      rw [Bool.not_eq_true] at h
      rw [h]
  · -- Y 1 = false, Y c = true : Y = !signBool
    right
    funext σ
    rw [hY σ]
    by_cases h : signBool σ = true
    · rw [if_pos h, h1, h]
      decide
    · rw [if_neg h, h2]
      rw [Bool.not_eq_true] at h
      rw [h]
      decide
  · -- Y 1 = false, Y c = false : constantly false, so prb Y true = 0
    exfalso
    have hconst : ∀ σ, Y σ = false := by
      intro σ
      rw [hY σ]
      by_cases h : signBool σ = true
      · rw [if_pos h]; exact h1
      · rw [if_neg h]; exact h2
    have he : fiber Y true = ∅ := by
      ext σ
      simp [fiber, hconst σ]
    rw [prb, he] at hbal
    norm_num at hbal
