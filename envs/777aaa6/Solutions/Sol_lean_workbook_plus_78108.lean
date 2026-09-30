-- Prove2me | solution 1 for lean_workbook_plus_78108
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:33:42.080971+00:00
-- url     : https://prove2.me/submissions/a3759e71-542d-4fdd-8d15-d9e1ad63f089

import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

theorem solution (f : ℝ → ℝ)
    (hpos : ∀ x : ℝ, 0 < x → 0 < f x)
    (hf : ∀ x y : ℝ, 0 < x ∧ 0 < y →
      f (x + y) ≤ (f x)^2 / (f x + y)) : False := by
  have h1 : 0 < f 1 := hpos 1 (by norm_num)
  let L : ℝ := 1 + 2 * f 1
  have hL : 0 < L := by dsimp [L]; linarith
  have hhalf (x : ℝ) (hx : 0 < x) :
      2 * f (x + f x) ≤ f x := by
    have hfx := hpos x hx
    have hd := (le_div_iff₀ (add_pos hfx hfx)).1 (hf x (f x) ⟨hx, hfx⟩)
    apply (mul_le_mul_iff_right₀ hfx).1
    nlinarith [hd]
  -- The potential bounds every iterate while the function values halve.
  have hw : ∀ n : ℕ, ∃ x : ℝ,
      0 < x ∧ x + 2 * f x ≤ L ∧ f x * (2 : ℝ)^n ≤ f 1 := by
    intro n
    induction n with
    | zero =>
      refine ⟨1, by norm_num, ?_, ?_⟩
      · exact le_refl _
      · simp
    | succ n ih =>
      obtain ⟨x, hx, hpot, hbound⟩ := ih
      have hfx := hpos x hx
      have hh := hhalf x hx
      refine ⟨x + f x, add_pos hx hfx, ?_, ?_⟩
      · linarith
      · have hmul := mul_le_mul_of_nonneg_right hh
          (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n)
        calc
          f (x + f x) * (2 : ℝ)^(n + 1)
              = (2 * f (x + f x)) * (2 : ℝ)^n := by rw [pow_succ]; ring
          _ ≤ f x * (2 : ℝ)^n := hmul
          _ ≤ f 1 := hbound
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (f 1 / f L) (by norm_num : (1 : ℝ) < 2)
  obtain ⟨x, hx, hpot, hbound⟩ := hw n
  have hfx := hpos x hx
  have hgap : 0 < L - x := by linarith
  have hden : 0 < f x + (L - x) := add_pos hfx hgap
  have hlower : f L ≤ f x := by
    calc
      f L = f (x + (L - x)) := by congr 1; ring
      _ ≤ (f x)^2 / (f x + (L - x)) := hf x (L - x) ⟨hx, hgap⟩
      _ ≤ f x := (div_le_iff₀ hden).2 (by
        nlinarith [mul_nonneg (le_of_lt hfx) (le_of_lt hgap)])
  have hmul := mul_le_mul_of_nonneg_right hlower
    (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n)
  have hstrict := (div_lt_iff₀ (hpos L hL)).1 hn
  nlinarith [hmul, hbound, hstrict]
