-- Prove2me | solution 1 for lean_workbook_plus_26056
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:31:44.029259+00:00
-- url     : https://prove2.me/submissions/843b11e4-1ace-4c37-bbb0-93174d645c6b

import Mathlib.Data.Finset.Card
import Mathlib.Tactic

private theorem mersenne_fixed (f : ℕ → ℕ) (h1 : f 1 = 1) (h3 : f 3 = 3)
    (hrec : ∀ n, f (4 * n + 3) = 3 * f (2 * n + 1) - 2 * f n) :
    ∀ k : ℕ, f (2 ^ (k + 1) - 1) = 2 ^ (k + 1) - 1 := by
  apply Nat.twoStepInduction
  · simpa using h1
  · simpa using h3
  · intro k ih0 ih1
    have hp : 0 < 2 ^ (k + 1) := pow_pos (by decide) _
    have hpow : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by
      rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
      omega
    have hpow' : 2 ^ (k + 3) = 4 * 2 ^ (k + 1) := by
      rw [show k + 3 = (k + 2) + 1 by omega, pow_succ, hpow]
      omega
    have harg : 4 * (2 ^ (k + 1) - 1) + 3 = 2 ^ (k + 3) - 1 := by omega
    have harg' : 2 * (2 ^ (k + 1) - 1) + 1 = 2 ^ (k + 2) - 1 := by omega
    change f (2 ^ (k + 3) - 1) = 2 ^ (k + 3) - 1
    rw [← harg, hrec, harg', ih0, ih1]
    omega

private theorem arbitrarily_many_fixed (f : ℕ → ℕ) (h1 : f 1 = 1) (h3 : f 3 = 3)
    (hrec : ∀ n, f (4 * n + 3) = 3 * f (2 * n + 1) - 2 * f n) (N : ℕ) :
    ∃ A : Finset ℕ, A.card = N ∧ ∀ n ∈ A, f n = n := by
  have hmono : StrictMono (fun k : ℕ => 2 ^ (k + 1) - 1) := by
    intro a b hab
    change 2 ^ (a + 1) - 1 < 2 ^ (b + 1) - 1
    have hp := Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega : a + 1 < b + 1)
    have hpos : 0 < 2 ^ (a + 1) := pow_pos (by decide) _
    omega
  refine ⟨(Finset.range N).image (fun k => 2 ^ (k + 1) - 1), ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hmono.injective, Finset.card_range]
  · intro n hn
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hn
    exact mersenne_fixed f h1 h3 hrec k

theorem solution (f : ℕ → ℕ) (h₀ : f 1 = 1) (h₁ : f 3 = 3)
    (_h₂ : ∀ n, f (2 * n) = f n)
    (_h₃ : ∀ n, f (4 * n + 1) = 2 * f (2 * n + 1) - f n)
    (h₄ : ∀ n, f (4 * n + 3) = 3 * f (2 * n + 1) - 2 * f n) :
    ∃ A : Finset ℕ, A.card = 1988 ∧ ∀ n ∈ A, f n = n :=
  arbitrarily_many_fixed f h₀ h₁ h₄ 1988
