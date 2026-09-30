-- Prove2me | solution 1 for lean_workbook_plus_14516
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T21:47:27.781208+00:00
-- url     : https://prove2.me/submissions/d865c752-9fe5-4e21-9bbd-54d3d4c4d718

import Mathlib

set_option autoImplicit false

namespace PositiveRationalSquareQuotient

def Equation (f : ℚ → ℝ) : Prop :=
  (∀ x > 0, 0 < f x) ∧
  ∀ x : ℚ, x > 0 → ∀ y : ℚ, y > 0 →
    2 * (x : ℝ) * (y : ℝ) = f (x + y) - f x - f (x * y) / f x

theorem strictMonoOn {f : ℚ → ℝ} (hf : Equation f) :
    StrictMonoOn f (Set.Ioi 0) := by
  intro x hx y _ hxy
  have hd : 0 < y - x := sub_pos.mpr hxy
  have h := hf.2 x hx (y - x) hd
  rw [add_sub_cancel] at h
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  have hdR : (0 : ℝ) < ((y - x : ℚ) : ℝ) := by exact_mod_cast hd
  have ht : 0 < 2 * (x : ℝ) * ((y - x : ℚ) : ℝ) := by positivity
  have hp : 0 < f (x * (y - x)) / f x := div_pos (hf.1 _ (mul_pos hx hd)) (hf.1 x hx)
  linarith

theorem mul_of_ne {f : ℚ → ℝ} (hf : Equation f) (x y : ℚ)
    (hx : 0 < x) (hy : 0 < y) (hne : x ≠ y) : f (x * y) = f x * f y := by
  have hfx : f x ≠ 0 := (hf.1 x hx).ne'
  have hfy : f y ≠ 0 := (hf.1 y hy).ne'
  have hne' : f x ≠ f y := fun he => hne ((strictMonoOn hf).injOn hx hy he)
  have hxy := hf.2 x hx y hy
  have hyx := hf.2 y hy x hx
  rw [add_comm y x, mul_comm y x] at hyx
  have he : f x + f (x * y) / f x = f y + f (x * y) / f y := by nlinarith only [hxy, hyx]
  field_simp at he
  have hz : (f x - f y) * (f (x * y) - f x * f y) = 0 := by nlinarith only [he]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hne'))

theorem one_value {f : ℚ → ℝ} (hf : Equation f) : f 1 = 1 := by
  have h := mul_of_ne hf 1 2 (by norm_num) (by norm_num) (by norm_num)
  norm_num at h
  have hp := hf.1 2 (by norm_num)
  nlinarith only [h, hp]

theorem unit_shift {f : ℚ → ℝ} (hf : Equation f) (x : ℚ) (hx : 0 < x) :
    f (x + 1) = f x + 2 * (x : ℝ) + 1 := by
  have h := hf.2 x hx 1 (by norm_num)
  simp only [Rat.cast_one, mul_one, div_self (hf.1 x hx).ne'] at h
  linarith

theorem nat_value {f : ℚ → ℝ} (hf : Equation f) (n : ℕ) (hn : 0 < n) :
    f n = (n : ℝ) ^ 2 := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hn0 : n = 0
    · subst n
      simpa using one_value hf
    have hn' : 0 < n := Nat.pos_of_ne_zero hn0
    have h := unit_shift hf n (by exact_mod_cast hn')
    rw [ih hn'] at h
    push_cast at h ⊢
    nlinarith only [h]

theorem fraction_value {f : ℚ → ℝ} (hf : Equation f) (m n : ℕ)
    (hm : 0 < m) (hn : 0 < n) : f ((m : ℚ) / n) = (((m : ℚ) / n : ℚ) : ℝ) ^ 2 := by
  have hnQ : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hp : (0 : ℚ) < (m : ℚ) / n := by positivity
  by_cases he : (m : ℚ) / n = n
  · rw [he]
    simpa using nat_value hf n hn
  have h := mul_of_ne hf ((m : ℚ) / n) n hp (by exact_mod_cast hn) he
  rw [div_mul_cancel₀ _ hnQ, nat_value hf m hm, nat_value hf n hn] at h
  apply (mul_right_cancel₀ (pow_ne_zero 2 hnR))
  rw [← h]
  push_cast
  field_simp

theorem positive_value {f : ℚ → ℝ} (hf : Equation f) (q : ℚ) (hq : 0 < q) :
    f q = (q : ℝ) ^ 2 := by
  have hn : 0 < q.num := Rat.num_pos.mpr hq
  have hm : 0 < q.num.toNat := by omega
  have he : ((q.num.toNat : ℕ) : ℚ) / q.den = q := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hn.le, Rat.num_div_den]
  simpa only [he] using fraction_value hf q.num.toNat q.den hm q.pos

theorem classification (f : ℚ → ℝ) : Equation f ↔ ∀ x : ℚ, x > 0 → f x = (x : ℝ) ^ 2 := by
  constructor
  · exact fun hf x hx => positive_value hf x hx
  · intro hf
    constructor
    · intro x hx
      rw [hf x hx]
      have hxR : (0 : ℝ) < x := by exact_mod_cast hx
      exact sq_pos_of_pos hxR
    · intro x hx y hy
      rw [hf (x + y) (add_pos hx hy), hf x hx, hf (x * y) (mul_pos hx hy)]
      have hxR : (x : ℝ) ≠ 0 := by exact_mod_cast hx.ne'
      push_cast
      field_simp
      ring

theorem multiplicative {f : ℚ → ℝ} (hf : Equation f) (x y : ℚ)
    (hx : 0 < x) (hy : 0 < y) : f (x * y) = f x * f y := by
  rw [positive_value hf (x * y) (mul_pos hx hy), positive_value hf x hx, positive_value hf y hy]
  push_cast
  ring

theorem extension (g : ℚ → ℝ) :
    Equation (fun x : ℚ => if 0 < x then (x : ℝ) ^ 2 else g x) := by
  apply (classification _).mpr
  intro x hx
  simp only [if_pos hx]

theorem extension_classification (f : ℚ → ℝ) :
    Equation f ↔ ∃ g : ℚ → ℝ, f = fun x : ℚ => if 0 < x then (x : ℝ) ^ 2 else g x := by
  constructor
  · intro hf
    refine ⟨f, funext fun x => ?_⟩
    split_ifs with hx
    · exact positive_value hf x hx
    · rfl
  · rintro ⟨g, rfl⟩
    exact extension g

theorem source_exists : ∃ f : ℚ → ℝ, Equation f :=
  ⟨fun x => (x : ℝ) ^ 2, (classification _).mpr (by intros; rfl)⟩

theorem posted_inconsistent (f : ℚ → ℝ)
    (hp : ∀ x > 0, 0 < f x)
    (hs : ∀ x : ℚ, x > 0 → 2 * (x : ℝ) = f (x + 1) - f x - f (x * 1))
    (hm : ∀ x > 0, ∀ y > 0, f (x * y) = f x * f y) : False := by
  have h1 := hm 1 (by norm_num) 1 (by norm_num)
  have hp1 := hp 1 (by norm_num)
  norm_num at h1
  have he : f 1 = 1 := by nlinarith only [h1, hp1]
  have h2 := hs 1 (by norm_num)
  have h3 := hs 2 (by norm_num)
  have h4 := hs 3 (by norm_num)
  have hh := hm 2 (by norm_num) 2 (by norm_num)
  norm_num [he] at h2 h3 h4 hh
  nlinarith only [h2, h3, h4, hh]

end PositiveRationalSquareQuotient

theorem solution (f : ℚ → ℝ)
    (h₀ : ∀ x > 0, f x > 0)
    (h₁ : ∀ x > 0, 2 * x = f (x + 1) - f x - f (x * 1))
    (h₂ : ∀ x > 0, ∀ y > 0, f (x * y) = f x * f y) :
    ∀ x > 0, f x = x ^ 2 := by
  exact (PositiveRationalSquareQuotient.posted_inconsistent f h₀ h₁ h₂).elim
